module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ProjectiveRepGroupHomologyPosVanishes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.Staircase

theorem main : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i → Function.Exact (d (p + 1)).hom (d p).hom) → (∀ p q, 1 ≤ p → p + q = i → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom) → Function.Surjective (hMap (d 0) i).hom := by
  intro k G _ _ i C d hd hd0 hexC hexH
  have ses : ∀ (W X Y : Rep.{0, 0, 0} k G) (u : W ⟶ X) (v : X ⟶ Y) (huv : u ≫ v = 0),
      Function.Exact u.hom v.hom →
      (ShortComplex.mk (kernel.ι u) (kernel.lift v u huv)
        (by rw [← cancel_mono (kernel.ι v)]; simp)).ShortExact := by
    intro W X Y u v huv hex
    have hS' : (ShortComplex.mk (kernel.ι u) u (kernel.condition u)).Exact :=
      ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel u)
    let φ : ShortComplex.mk (kernel.ι u) (kernel.lift v u huv)
        (by rw [← cancel_mono (kernel.ι v)]; simp) ⟶
        ShortComplex.mk (kernel.ι u) u (kernel.condition u) :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι v, comm₁₂ := by simp, comm₂₃ := by simp }
    have hinj : Function.Injective (kernel.ι v).hom := (Rep.mono_iff_injective _).mp inferInstance
    refine { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hS',
             mono_f := inferInstance, epi_g := ?_ }
    rw [Rep.epi_iff_surjective]
    intro z
    have hz : v.hom ((kernel.ι v).hom z) = 0 := by
      have h := congrArg (fun f => f.hom z) (kernel.condition v)
      simpa using h
    obtain ⟨y, hy⟩ := (hex _).mp hz
    refine ⟨y, hinj ?_⟩
    have h := congrArg (fun f => f.hom y) (kernel.lift_ι v u huv)
    exact h.trans hy
  have epi0 : ∀ (X Y : Rep.{0, 0, 0} k G) (f : X ⟶ Y), Function.Surjective f.hom →
      Function.Surjective (hMap f 0).hom := by
    intro X Y f hf
    haveI : Epi f := (Rep.epi_iff_surjective f).mpr hf
    exact (ModuleCat.epi_iff_surjective _).mp (groupHomology.epi_map_0_of_epi f)
  have liftSurj : ∀ p, p + 1 ≤ i →
      Function.Surjective (kernel.lift (d p) (d (p + 1)) (hd p)).hom := by
    intro p hp
    exact (Rep.epi_iff_surjective _).mp (ses _ _ _ (d (p + 1)) (d p) (hd p) (hexC p hp)).epi_g
  have R : ∀ q p, p + 1 + q = i →
      Function.Surjective (hMap (kernel.lift (d p) (d (p + 1)) (hd p)) q).hom := by
    intro q
    induction q with
    | zero =>
      intro p hp
      exact epi0 _ _ _ (liftSurj p (by omega))
    | succ q ih =>
      intro p hp
      have hab : d (p + 3) ≫ kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1)) = 0 := by
        rw [← cancel_mono (kernel.ι (d (p + 1)))]
        simp [hd]
      have hbι : kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1)) ≫ kernel.ι (d (p + 1)) =
          d (p + 2) := kernel.lift_ι _ _ _
      have hE : Function.Exact (hMap (d (p + 3)) q).hom
          (hMap (kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1)) ≫ kernel.ι (d (p + 1))) q).hom := by
        rw [hbι]
        exact hexH (p + 2) q (by omega) (by omega)
      exact homStab_step k G (C (p + 4)) (C (p + 3)) (kernel (d (p + 1))) (C (p + 2)) (kernel (d p))
        (d (p + 3)) (kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1))) (kernel.ι (d (p + 1)))
        (kernel.lift (d p) (d (p + 1)) (hd p)) _
        (ses _ _ _ (d (p + 1)) (d p) (hd p) (hexC p (by omega))) hab q (ih (p + 1) (by omega)) hE
  cases i with
  | zero => exact epi0 _ _ _ hd0
  | succ q =>
    have ses0 : (ShortComplex.mk (kernel.ι (d 0)) (d 0) (kernel.condition _)).ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (d 0))
        mono_f := inferInstance
        epi_g := (Rep.epi_iff_surjective _).mpr hd0 }
    have hab : d 2 ≫ kernel.lift (d 0) (d 1) (hd 0) = 0 := by
      rw [← cancel_mono (kernel.ι (d 0))]
      simp [hd]
    have hbι : kernel.lift (d 0) (d 1) (hd 0) ≫ kernel.ι (d 0) = d 1 := kernel.lift_ι _ _ _
    have hE : Function.Exact (hMap (d 2) q).hom
        (hMap (kernel.lift (d 0) (d 1) (hd 0) ≫ kernel.ι (d 0)) q).hom := by
      rw [hbι]
      exact hexH 1 q (by omega) (by omega)
    exact homStab_step k G (C 3) (C 2) (kernel (d 0)) (C 1) (C 0) (d 2)
      (kernel.lift (d 0) (d 1) (hd 0)) (kernel.ι (d 0)) (d 0) _ ses0 hab q (R q 0 (by omega)) hE

end GlobalTheory.HomStab.Staircase

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.surjective_hMap_zero_of_staircase : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i → Function.Exact (d (p + 1)).hom (d p).hom) → (∀ p q, 1 ≤ p → p + q = i → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom) → Function.Surjective (hMap (d 0) i).hom := by
  first
  | exact @GlobalTheory.HomStab.Staircase.main
end
end

section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem shapiro_pt : ∀ (k G H X : Type) [CommRing k] [Group G] [Group H] [MulAction G X] (φ : H →* G) (x : X) (hx : ∀ h, φ h • x = x), Function.Injective φ → φ.range = MulAction.stabilizer G x → (∀ y : X, ∃ g : G, g • x = y) → (∀ (n : ℕ) (A : Rep k G), IsIso (groupHomology.map φ (ptMap φ x hx A) n)) ∧ ∀ n : ℕ, IsIso (ptH (k := k) φ x hx n) := by
  intro k G H X _ _ _ _ φ x hx hi hr ht
  have key : ∀ (n : ℕ) (A : Rep k G), IsIso (groupHomology.map φ (ptMap φ x hx A) n) := by
    intro n
    induction n with
    | zero => exact fun A => GlobalTheory.T.shapiro_isIso_groupHomology_zero k G H X φ x hx hr ht A
    | succ n ih =>
      intro A
      obtain ⟨ι, K, i, e, h, hS⟩ := GlobalTheory.T.exists_free_resolution_short_exact k G A
      have hX := hS.map_of_exact (Rep.resFunctor (k := k) φ)
      obtain ⟨hz, hY⟩ := GlobalTheory.T.permCoef_preserves_shortExact k G X _ hS
      refine GlobalTheory.T.groupHomology_dimension_shift_isIso k G H φ _ _ hX hY (ptMap φ x hx K) (ptMap φ x hx (Rep.free k G ι))
        (ptMap φ x hx A) ?_ ?_ n (GlobalTheory.T.projective_rep_groupHomology_pos_vanishes k H _ (GlobalTheory.T.projective_res_free_rep_of_injective k G H φ hi ι) n)
        (GlobalTheory.T.projective_rep_groupHomology_pos_vanishes k G _ (GlobalTheory.T.projective_perm_tensor_free k G X ι) n) (ih K) (ih _)
      · intro a
        exact (Finsupp.mapRange_single (hf := map_zero (Rep.Hom.hom i))).symm
      · intro a
        exact (Finsupp.mapRange_single (hf := map_zero (Rep.Hom.hom e))).symm
  exact ⟨key, fun n => key n (Rep.trivial k G k)⟩

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.shapiro_lemma_transitive_groupHomology : ∀ (k G H X : Type) [CommRing k] [Group G] [Group H] [MulAction G X] (φ : H →* G) (x : X) (hx : ∀ h, φ h • x = x), Function.Injective φ → φ.range = MulAction.stabilizer G x → (∀ y : X, ∃ g : G, g • x = y) → (∀ (n : ℕ) (A : Rep k G), IsIso (groupHomology.map φ (ptMap φ x hx A) n)) ∧ ∀ n : ℕ, IsIso (ptH (k := k) φ x hx n) := by
  first
  | exact @GlobalTheory.HomStab.shapiro_pt
end
end

section

open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory.SplitStd

variable {R : Type} [CommRing R]

def extLast (m : ℕ) : Matrix (Fin m) (Fin m) R →* Matrix (Fin (m + 1)) (Fin (m + 1)) R where
  toFun A := Matrix.of fun i j =>
    Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j) (fun i' => Fin.lastCases 0 (fun j' => A i' j') j) i
  map_one' := by
    ext i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
  map_mul' A B := by
    ext i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_castSucc]

theorem extLast_mulVec_single_last (m : ℕ) (A : Matrix (Fin m) (Fin m) R) :
    extLast m A *ᵥ Pi.single (Fin.last m) 1 = Pi.single (Fin.last m) 1 := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    simp [extLast, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.castSucc_ne_last]

theorem single_last_vecMul_extLast (m : ℕ) (A : Matrix (Fin m) (Fin m) R) :
    Pi.single (Fin.last m) 1 ᵥ* extLast m A = Pi.single (Fin.last m) 1 := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    simp [extLast, Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc, Fin.castSucc_ne_last]

theorem extLast_mulVec (m : ℕ) (A : Matrix (Fin m) (Fin m) R) (w : Fin (m + 1) → R)
    (hw : w (Fin.last m) = 0) (a : Fin m) (h : A *ᵥ (fun i => w i.castSucc) = Pi.single a 1) :
    extLast m A *ᵥ w = Pi.single a.castSucc 1 := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [extLast, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hw, (Fin.castSucc_ne_last a).symm]
  · have := congrFun h i
    simp only [Matrix.mulVec, dotProduct] at this
    simp [extLast, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hw, this, Pi.single_apply]

theorem vecMul_extLast (m : ℕ) (A : Matrix (Fin m) (Fin m) R) (w : Fin (m + 1) → R)
    (hw : w (Fin.last m) = 0) (a : Fin m) (h : (fun i => w i.castSucc) ᵥ* A = Pi.single a 1) :
    w ᵥ* extLast m A = Pi.single a.castSucc 1 := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [extLast, Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc, hw, (Fin.castSucc_ne_last a).symm]
  · have := congrFun h i
    simp only [Matrix.vecMul, dotProduct] at this
    simp [extLast, Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc, hw, this, Pi.single_apply]

theorem dot_conj {k : ℕ} (g : GL (Fin k) R) (f v : Fin k → R) :
    (f ᵥ* ((g⁻¹ : GL (Fin k) R) : Matrix (Fin k) (Fin k) R)) ⬝ᵥ ((g : Matrix (Fin k) (Fin k) R) *ᵥ v)
      = f ⬝ᵥ v := by
  rw [← dotProduct_mulVec, mulVec_mulVec, Units.inv_mul, one_mulVec]

theorem core (s : ℕ) (hs : StableRangeLe R s) : ∀ (k m : ℕ) (v f : Fin k → Fin m → R),
    (∀ i j, f i ⬝ᵥ v j = if i = j then 1 else 0) → k + s ≤ m →
    ∃ (g : GL (Fin m) R) (σ : Fin k → Fin m), Function.Injective σ ∧ ∀ j,
      (g : Matrix (Fin m) (Fin m) R) *ᵥ v j = Pi.single (σ j) 1 ∧
      f j ᵥ* ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) = Pi.single (σ j) 1 := by
  intro k
  induction k with
  | zero => intro m v f _ _; exact ⟨1, Fin.elim0, fun a => a.elim0, fun j => j.elim0⟩
  | succ k ih =>
    intro m v f hvf hkm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨g₁, hg₁v, hg₁f⟩ := GlobalTheory.T.exists_GL_moving_unimodular_pair_to_last_basis R s hs m (by omega) (v 0) (f 0) (by simpa using hvf 0 0)
    have hvl : ∀ j : Fin k, ((g₁ : Matrix _ _ R) *ᵥ v j.succ) (Fin.last m) = 0 := by
      intro j
      have key := dot_conj g₁ (f 0) (v j.succ)
      rw [hg₁f, single_dotProduct, one_mul, hvf, if_neg (Fin.succ_ne_zero j).symm] at key
      exact key
    have hfl : ∀ j : Fin k, (f j.succ ᵥ* ((g₁⁻¹ : GL _ R) : Matrix _ _ R)) (Fin.last m) = 0 := by
      intro j
      have key := dot_conj g₁ (f j.succ) (v 0)
      rw [hg₁v, dotProduct_single, mul_one, hvf, if_neg (Fin.succ_ne_zero j)] at key
      exact key
    let v' : Fin k → Fin m → R := fun j i => ((g₁ : Matrix _ _ R) *ᵥ v j.succ) i.castSucc
    let f' : Fin k → Fin m → R := fun j i => (f j.succ ᵥ* ((g₁⁻¹ : GL _ R) : Matrix _ _ R)) i.castSucc
    have hdual : ∀ i j, f' i ⬝ᵥ v' j = if i = j then 1 else 0 := by
      intro i j
      have key := dot_conj g₁ (f i.succ) (v j.succ)
      rw [hvf, dotProduct, Fin.sum_univ_castSucc, hvl j, mul_zero, add_zero] at key
      simpa [dotProduct, v', f', Fin.succ_inj] using key
    obtain ⟨g', σ', hσ', hg'⟩ := ih m v' f' hdual (by omega)
    refine ⟨Units.map (extLast m) g' * g₁,
      (Fin.cons (Fin.last m) (fun j => (σ' j).castSucc) : Fin (k + 1) → Fin (m + 1)), ?_, ?_⟩
    · rw [Fin.cons_injective_iff]
      refine ⟨?_, (Fin.castSucc_injective _).comp hσ'⟩
      rintro ⟨j, hj⟩
      exact Fin.castSucc_ne_last _ hj
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.cons_zero, _root_.mul_inv_rev, Units.val_mul, Units.coe_map, Units.coe_map_inv]
        refine ⟨?_, ?_⟩
        · rw [← mulVec_mulVec, hg₁v, extLast_mulVec_single_last]
        · rw [← vecMul_vecMul, hg₁f, single_last_vecMul_extLast]
      · simp only [Fin.cons_succ, _root_.mul_inv_rev, Units.val_mul, Units.coe_map, Units.coe_map_inv]
        refine ⟨?_, ?_⟩
        · rw [← mulVec_mulVec]
          exact extLast_mulVec m _ _ (hvl j) _ (hg' j).1
        · rw [← vecMul_vecMul]
          exact vecMul_extLast m _ _ (hfl j) _ (hg' j).2

def pmat {n : ℕ} (π : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if i = π j then 1 else 0

theorem pmat_mul_symm {n : ℕ} (π : Equiv.Perm (Fin n)) : (pmat π : Matrix (Fin n) (Fin n) R) * pmat π.symm = 1 := by
  ext i j
  simp [pmat, Matrix.mul_apply, Matrix.one_apply, Equiv.apply_eq_iff_eq_symm_apply]

def pGL {n : ℕ} (π : Equiv.Perm (Fin n)) : GL (Fin n) R :=
  ⟨pmat π, pmat π.symm, pmat_mul_symm π, by simpa using pmat_mul_symm (R := R) π.symm⟩

theorem pGL_mulVec {n : ℕ} (π : Equiv.Perm (Fin n)) (a : Fin n) :
    ((pGL π : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ Pi.single a 1 = Pi.single (π a) 1 := by
  funext i
  simp only [pGL, pmat, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single a]
  · simp [Pi.single_apply]
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

theorem vecMul_pGL_inv {n : ℕ} (π : Equiv.Perm (Fin n)) (a : Fin n) :
    Pi.single a 1 ᵥ* (((pGL π)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Pi.single (π a) 1 := by
  funext i
  simp only [pGL, pmat, Matrix.vecMul, dotProduct, Matrix.of_apply, Units.inv_mk]
  rw [Finset.sum_eq_single a]
  · simp [Pi.single_apply, Equiv.eq_symm_apply, eq_comm]
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

theorem exists_perm {n k : ℕ} (σ ι : Fin k → Fin n) (hσ : Function.Injective σ) (hι : Function.Injective ι) :
    ∃ π : Equiv.Perm (Fin n), ∀ j, π (σ j) = ι j := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨1, fun j => j.elim0⟩
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq (t := (Finset.univ : Finset (Fin n)))
    (s := Finset.univ.image σ) (f := fun x => ι (Function.invFun σ x)) (by simp)
    (fun _ _ => Finset.mem_univ _) (by
      intro x hx y hy hxy
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      simp only [Function.leftInverse_invFun hσ a, Function.leftInverse_invFun hσ b] at hxy
      rw [hι hxy])
  refine ⟨g.trans (Equiv.subtypeUnivEquiv Finset.mem_univ), fun j => ?_⟩
  have := hg (σ j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  simpa [Function.leftInverse_invFun hσ j] using this

end GlobalTheory.SplitStd

open GlobalTheory.SplitStd in
theorem GlobalTheory.splitSeq_to_standard : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n : ℕ) (l : List ((Fin n → R) × (Fin n → R))), l ∈ splitSeq R n → l.length + s ≤ n → ∀ ι : Fin l.length → Fin n, Function.Injective ι → ∃ g : GL (Fin n) R, ∀ j : Fin l.length, (g : Matrix (Fin n) (Fin n) R) *ᵥ (l.get j).1 = Pi.single (ι j) 1 ∧ (l.get j).2 ᵥ* ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Pi.single (ι j) 1 := by
  intro R _ s hs n l hl hlen ι hι
  obtain ⟨g, σ, hσ, hg⟩ := core s hs l.length n (fun j => (l.get j).1) (fun j => (l.get j).2) hl hlen
  obtain ⟨π, hπ⟩ := exists_perm σ ι hσ hι
  refine ⟨pGL π * g, fun j => ⟨?_, ?_⟩⟩
  · rw [Units.val_mul, ← mulVec_mulVec, (hg j).1, pGL_mulVec, hπ]
  · rw [_root_.mul_inv_rev, Units.val_mul, ← vecMul_vecMul, (hg j).2, vecMul_pGL_inv, hπ]

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exists_GL_splitSeq_standard_of_stableRangeLe : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n : ℕ) (l : List ((Fin n → R) × (Fin n → R))), l ∈ splitSeq R n → l.length + s ≤ n → ∀ ι : Fin l.length → Fin n, Function.Injective ι → ∃ g : GL (Fin n) R, ∀ j : Fin l.length, (g : Matrix (Fin n) (Fin n) R) *ᵥ (l.get j).1 = Pi.single (ι j) 1 ∧ (l.get j).2 ᵥ* ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Pi.single (ι j) 1 := by
  first
  | exact @GlobalTheory.splitSeq_to_standard
end
end

section

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.UniModVec

theorem mem_uniM_iff_nat (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (l : List M) :
    l ∈ uniM R M ↔ ∃ f : ℕ → M →ₗ[R] R, ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length),
      f i l[j] = if i = j then 1 else 0 := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun i => if h : i < l.length then f ⟨i, h⟩ else 0, fun i j hi hj => ?_⟩
    have := hf ⟨i, hi⟩ ⟨j, hj⟩
    simp only [hi, dif_pos]
    simpa [Fin.ext_iff] using this
  · rintro ⟨f, hf⟩
    refine ⟨fun i => f i, fun i j => ?_⟩
    have := hf i j i.isLt j.isLt
    simpa [Fin.ext_iff] using this

end GlobalTheory.UniModVec

namespace GlobalTheory.UniModVec

theorem cons_mem_uniM_iff_map_proj : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) (v : M), φ v = 1 → ∀ l : List M, (v :: l) ∈ uniM R M ↔ l.map (fun x => x - φ x • v) ∈ uniM R M := by
  intro R M _ _ _ φ v hv l
  rw [mem_uniM_iff_nat, mem_uniM_iff_nat]
  constructor
  · rintro ⟨F, hF⟩
    refine ⟨fun i => F (i+1), fun i j hi hj => ?_⟩
    simp only [List.length_map] at hi hj
    have h1 := hF (i+1) (j+1) (by simp; omega) (by simp; omega)
    have h2 := hF (i+1) 0 (by simp; omega) (by simp)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h1 h2
    simp only [List.getElem_map, map_sub, map_smul, smul_eq_mul, h1, h2]
    simp
  · rintro ⟨H, hH⟩
    simp only [List.length_map, List.getElem_map] at hH
    let P : M →ₗ[R] M := LinearMap.id - φ.smulRight v
    have hP : ∀ x, P x = x - φ x • v := fun x => by simp [P]
    have hPv : P v = 0 := by rw [hP, hv, one_smul, sub_self]
    let F : ℕ → M →ₗ[R] R := fun i => match i with
      | 0 => φ - ∑ k : Fin l.length, φ (l.get k) • (H k).comp P
      | k+1 => (H k).comp P
    refine ⟨F, fun i j hi hj => ?_⟩
    simp only [List.length_cons] at hi hj
    rcases i with _ | i <;> rcases j with _ | j
    · simp [F, hPv, hv]
    · have hj' : j < l.length := by omega
      have hF0 : F 0 (l[j]) = φ l[j] - ∑ k : Fin l.length, φ (l.get k) * H k (l[j] - φ l[j] • v) := by
        simp only [F, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
          LinearMap.comp_apply, hP, smul_eq_mul]
      simp only [List.getElem_cons_succ]
      rw [hF0, Finset.sum_eq_single ⟨j, hj'⟩]
      · rw [hH j j hj' hj']; simp
      · intro k _ hk
        rw [hH k j k.isLt hj', if_neg (fun h => hk (Fin.ext h)), mul_zero]
      · simp
    · simp [F, hPv]
    · have hi' : i < l.length := by omega
      have hj' : j < l.length := by omega
      simp only [F, List.getElem_cons_succ, LinearMap.comp_apply, hP, hH i j hi' hj']
      simp

end GlobalTheory.UniModVec

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.cons_mem_uniM_iff_map_sub_smul : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) (v : M), φ v = 1 → ∀ l : List M, (v :: l) ∈ uniM R M ↔ l.map (fun x => x - φ x • v) ∈ uniM R M := by
  first
  | exact @GlobalTheory.UniModVec.cons_mem_uniM_iff_map_proj
  | exact @GlobalTheory.UniModVec.mem_uniM_iff_nat
end
end

section

namespace GlobalTheory.SeqCx

theorem cycle_pair_empty (V W : Type) (D : Set (List V × List W)) (p : ℕ) (c : List V →₀ ℤ)
    (hc : c ∈ chains {l | (l, ([] : List W)) ∈ D} p) (hb : bd V c = 0) :
    Finsupp.mapDomain (fun l => (l, ([] : List W))) c ∈ chains2 D p 0 ∧
      hbd V W (Finsupp.mapDomain (fun l => (l, ([] : List W))) c) = 0 ∧
      vbd V W (Finsupp.mapDomain (fun l => (l, ([] : List W))) c) = 0 := by
  have hlin : ∀ d : List V →₀ ℤ, Finsupp.mapDomain (fun l => (l, ([] : List W))) d
      = Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W))) d := fun d => rfl
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [chains2, Finsupp.mem_supported]
    rw [chains, Finsupp.mem_supported] at hc
    intro z hz
    have hz' := Finsupp.mapDomain_support hz
    rw [Finset.mem_image] at hz'
    obtain ⟨l, hl, rfl⟩ := hz'
    have := hc (Finset.mem_coe.mpr hl)
    exact ⟨this.1, this.2, rfl⟩
  · have key : (hbd V W).comp (Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W))))
        = (Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W)))).comp (bd V) := by
      apply Finsupp.lhom_ext'
      intro l
      apply LinearMap.ext_ring
      simp [hbd, Finsupp.mapDomain_single]
    have := LinearMap.congr_fun key c
    simp only [LinearMap.comp_apply] at this
    rw [hlin, this, hb, map_zero]
  · have key : (vbd V W).comp (Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W)))) = 0 := by
      apply Finsupp.lhom_ext'
      intro l
      apply LinearMap.ext_ring
      simp [vbd, bd, Finsupp.mapDomain_single]
    have := LinearMap.congr_fun key c
    simpa [LinearMap.comp_apply] using this

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.pair_nil_hbd_vbd_eq_zero_of_cycle : ∀ (V W : Type) (D : Set (List V × List W)) (p : ℕ) (c : List V →₀ ℤ), c ∈ chains {l | (l, ([] : List W)) ∈ D} p → bd V c = 0 → Finsupp.mapDomain (fun l => (l, ([] : List W))) c ∈ chains2 D p 0 ∧ hbd V W (Finsupp.mapDomain (fun l => (l, ([] : List W))) c) = 0 ∧ vbd V W (Finsupp.mapDomain (fun l => (l, ([] : List W))) c) = 0 := by
  first
  | exact @GlobalTheory.SeqCx.cycle_pair_empty
end
end
