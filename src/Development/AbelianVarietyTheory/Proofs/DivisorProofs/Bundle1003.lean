module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003

@[expose] public section

section

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.LogDR.StabTheta

variable {K : Type} [Field K]

theorem smul_mem_spanForms (M M' : Set K) (H : Set Ω[K⁄ℤ]) (a : ℕ) (c : K)
    (h : ∀ m ∈ M, c * m ∈ M') {η : abelian₂ K} (hη : η ∈ spanForms M H a) :
    c • η ∈ spanForms M' H a := by
  have key : spanForms M H a ≤
      (spanForms M' H a).comap (DistribSMul.toAddMonoidHom (abelian₂ K) c) := by
    unfold spanForms
    rw [AddSubgroup.closure_le]
    rintro _ ⟨m, hm, v, hv, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    show c • (m • ExteriorAlgebra.ιMulti K a v) ∈ AddSubgroup.closure _
    rw [smul_smul]
    exact AddSubgroup.subset_closure ⟨c * m, h m hm, v, hv, rfl⟩
  exact key hη

theorem iota_mul_mem_spanForms (M : Set K) (H : Set Ω[K⁄ℤ]) (q : ℕ) (w : Ω[K⁄ℤ]) (hw : w ∈ H)
    {η : abelian₂ K} (hη : η ∈ spanForms M H q) :
    ExteriorAlgebra.ι K w * η ∈ spanForms M H (q + 1) := by
  have key : spanForms M H q ≤
      (spanForms M H (q + 1)).comap (AddMonoidHom.mulLeft (ExteriorAlgebra.ι K w)) := by
    unfold spanForms
    rw [AddSubgroup.closure_le]
    rintro _ ⟨m, hm, v, hv, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    show ExteriorAlgebra.ι K w * (m • ExteriorAlgebra.ιMulti K q v) ∈ AddSubgroup.closure _
    rw [mul_smul_comm]
    refine AddSubgroup.subset_closure ⟨m, hm, Fin.cons w v, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hw
      · simpa using hv k
    · rw [ExteriorAlgebra.ιMulti_succ_apply]
      simp [Matrix.vecTail]
  exact key hη

theorem theta_dlog {n : ℕ} (x : Fin n → Kˣ) (i : Fin n) (θ : abelian₂ K →ₗ[K] abelian₂ K)
    (hθ : IsEulerContraction x i θ) (j : Fin n) :
    θ (ExteriorAlgebra.ι K (dlog (x j))) = algebraMap K (abelian₂ K) (if j = i then 1 else 0) := by
  rw [hθ.2.2 j]
  split_ifs <;> simp

theorem theta_frame (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n)
    (θ : abelian₂ K →ₗ[K] abelian₂ K) (hx : ∀ j, (x j : K) ∈ A) (hθ : IsEulerContraction x i θ) (j : Fin n) :
    ∃ a ∈ A, θ (ExteriorAlgebra.ι K (frame x J j)) = algebraMap K (abelian₂ K) a := by
  have hif : (if j = i then (1 : K) else 0) ∈ A := by split_ifs <;> simp
  unfold frame
  split_ifs with hj
  · exact ⟨_, hif, theta_dlog x i θ hθ j⟩
  · have hd : dK (x j : K) = (x j : K) • dlog (x j) := by
      unfold dlog
      rw [smul_smul]
      simp
    refine ⟨(x j : K) * (if j = i then 1 else 0), A.mul_mem (hx j) hif, ?_⟩
    rw [hd, map_smul, map_smul, theta_dlog x i θ hθ j, Algebra.smul_def, ← map_mul]

theorem theta_iotaMulti (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n)
    (θ : abelian₂ K →ₗ[K] abelian₂ K) (hx : ∀ j, (x j : K) ∈ A) (hθ : IsEulerContraction x i θ) :
    ∀ (q : ℕ) (v : Fin (q + 1) → Ω[K⁄ℤ]), (∀ k, v k ∈ Set.range (frame x J)) →
      θ (ExteriorAlgebra.ιMulti K (q + 1) v) ∈ spanForms (A : Set K) (Set.range (frame x J)) q := by
  intro q
  induction q with
  | zero =>
    intro v hv
    rw [ExteriorAlgebra.ιMulti_succ_apply, hθ.2.1, ExteriorAlgebra.ιMulti_zero_apply, hθ.1,
      mul_zero, sub_zero, mul_one]
    obtain ⟨j, hj⟩ := hv 0
    obtain ⟨a, ha, he⟩ := theta_frame A x J i θ hx hθ j
    rw [← hj, he, Algebra.algebraMap_eq_smul_one]
    refine AddSubgroup.subset_closure ⟨a, ha, Matrix.vecTail v, fun k => k.elim0, ?_⟩
    rw [ExteriorAlgebra.ιMulti_zero_apply]
  | succ q ih =>
    intro v hv
    rw [ExteriorAlgebra.ιMulti_succ_apply, hθ.2.1]
    obtain ⟨j, hj⟩ := hv 0
    obtain ⟨a, ha, he⟩ := theta_frame A x J i θ hx hθ j
    have htail : ∀ k, Matrix.vecTail v k ∈ Set.range (frame x J) := fun k => hv k.succ
    refine AddSubgroup.sub_mem _ ?_ ?_
    · rw [← hj, he, ← Algebra.smul_def]
      exact AddSubgroup.subset_closure ⟨a, ha, Matrix.vecTail v, htail, rfl⟩
    · exact iota_mul_mem_spanForms _ _ q _ (hv 0) (ih _ htail)

end GlobalTheory.LogDR.StabTheta

open GlobalTheory.LogDR.StabTheta in
theorem GlobalTheory.LogDR.chartForms_stable_euler :
    ∀ (K : Type) [Field K] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (i : Fin n) (θ : abelian₂ K →ₗ[K] abelian₂ K), (∀ j, (x j : K) ∈ A) → IsEulerContraction x i θ → (∀ q, ∀ η ∈ chartForms A x J t (q + 1), θ η ∈ chartForms A x J t q) ∧ ∀ η ∈ chartForms A x J t 0, θ η = 0 := by
  intro K _ A n x J t i θ hx hθ
  constructor
  · intro q η hη
    have key : chartForms A x J t (q + 1) ≤ (chartForms A x J t q).comap θ.toAddMonoidHom := by
      unfold chartForms spanForms
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, v, hv, rfl⟩
      rw [SetLike.mem_coe, AddSubgroup.mem_comap]
      show θ (c • ExteriorAlgebra.ιMulti K (q + 1) v) ∈ spanForms _ _ q
      rw [map_smul]
      refine smul_mem_spanForms (A : Set K) _ _ q c ?_ (theta_iotaMulti A x J i θ hx hθ q v hv)
      intro m hm
      show c * m * (t : K) ∈ A
      rw [mul_right_comm]
      exact A.mul_mem hc hm
    exact key hη
  · intro η hη
    have key : chartForms A x J t 0 ≤ θ.toAddMonoidHom.ker := by
      unfold chartForms spanForms
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, v, hv, rfl⟩
      rw [SetLike.mem_coe, AddMonoidHom.mem_ker]
      show θ (c • ExteriorAlgebra.ιMulti K 0 v) = 0
      rw [map_smul, ExteriorAlgebra.ιMulti_zero_apply, hθ.1, smul_zero]
    exact key hη
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR.ChartStalk

section Algebra

variable {K : Type} [Field K]

def IsComb (A : Subring K) (H' : Set Ω[K⁄ℤ]) (v : Ω[K⁄ℤ]) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → K) (w : ι → Ω[K⁄ℤ]),
    (∀ k, c k ∈ A) ∧ (∀ k, w k ∈ H') ∧ v = ∑ k, c k • w k

theorem isComb_single {A : Subring K} {H' : Set Ω[K⁄ℤ]} {v w : Ω[K⁄ℤ]} {c : K} (hc : c ∈ A)
    (hw : w ∈ H') (e : v = c • w) : IsComb A H' v :=
  ⟨Unit, inferInstance, fun _ => c, fun _ => w, fun _ => hc, fun _ => hw, by
    simp [Finset.univ_unique, e]⟩

theorem spanForms_le_of_isComb (A : Subring K) {M : Set K} {H H' : Set Ω[K⁄ℤ]} (a : ℕ)
    (hM : ∀ c ∈ M, ∀ b ∈ A, c * b ∈ M) (hH : ∀ v ∈ H, IsComb A H' v) :
    spanForms M H a ≤ spanForms M H' a := by
  unfold spanForms
  rw [AddSubgroup.closure_le]
  rintro η ⟨c, hc, v, hv, rfl⟩
  choose ι ft co w hco hw hv' using fun i => hH (v i) (hv i)
  have e : ExteriorAlgebra.ιMulti K a v = ∑ r : ∀ i, ι i,
      (∏ i, co i (r i)) • ExteriorAlgebra.ιMulti K a (fun i => w i (r i)) := by
    conv_lhs => rw [show v = fun i => ∑ k, co i k • w i k from funext hv']

    rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MultilinearMap.map_smul_univ]
    simp only [RingHom.id_apply]
  rw [e, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun r _ => AddSubgroup.subset_closure
    ⟨c * ∏ i, co i (r i), hM c hc _ (Subring.prod_mem _ fun i _ => hco i (r i)),
      fun i => w i (r i), fun i => hw i (r i), by rw [smul_smul]⟩

theorem dlog_one : dlog (1 : Kˣ) = 0 := by
  simp [dlog, dK]

theorem dlog_mul (g h : Kˣ) : dlog (g * h) = dlog g + dlog h := by
  simp only [dlog, dK, Units.val_mul, Derivation.leibniz, smul_add, smul_smul, mul_inv_rev,
    Units.val_inv_eq_inv_val]
  rw [add_comm]
  congr 2
  · field_simp
  · field_simp

def dlogHom : Kˣ →* Multiplicative Ω[K⁄ℤ] where
  toFun g := Multiplicative.ofAdd (dlog g)
  map_one' := by rw [dlog_one]; rfl
  map_mul' g h := by rw [dlog_mul]; rfl

theorem dlog_zpow (g : Kˣ) (m : ℤ) : dlog (g ^ m) = m • dlog g := by
  have := map_zpow (dlogHom (K := K)) g m
  exact congrArg Multiplicative.toAdd this

theorem dlog_prod {ι : Type} (s : Finset ι) (g : ι → Kˣ) : dlog (∏ i ∈ s, g i) = ∑ i ∈ s, dlog (g i) := by
  have := map_prod (dlogHom (K := K)) g s
  exact congrArg Multiplicative.toAdd this

theorem smul_dlog (g : Kˣ) : (g : K) • dlog g = dK (g : K) := by
  rw [dlog, smul_smul, Units.mul_inv, one_smul]

end Algebra

section Scheme

variable {X : Scheme.{0}} [IsIntegral X]

theorem dK_eq_frame {n : ℕ} (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n)) (i : Fin n) :
    dK (x i : X.functionField) = (if i ∈ J then (x i : X.functionField) else 1) • frame x J i := by
  unfold frame
  split_ifs with h
  · exact (smul_dlog (x i)).symm
  · rw [one_smul]

theorem isComb_dlog {Z : Set X} {U : X.Opens} {n : ℕ} {x : Fin n → X.functionFieldˣ} {J : Finset (Fin n)}
    (hc : IsLogChart Z U x J) {y : X} (hy : y ∈ U) {g : X.functionFieldˣ} (hg : LogUnit Z y g) :
    IsComb (locRing y) (Set.range (frame x J)) (dlog g) := by
  obtain ⟨u, m, hu, rfl⟩ := (hc.logUnit y hy g).1 hg
  obtain ⟨d, hd, hdu⟩ := (hc.chart y hy).deriv (u : X.functionField) hu.regAt
  refine ⟨Fin n, inferInstance,
    fun i => (u : X.functionField)⁻¹ * d i * (if i ∈ J then (x i : X.functionField) else 1) +
      (if i ∈ J then ((m i : ℤ) : X.functionField) else 0),
    frame x J, fun i => ?_, fun i => ⟨i, rfl⟩, ?_⟩
  · refine add_mem (mul_mem (mul_mem hu.inv.regAt (hd i)) ?_) ?_
    · split_ifs
      · exact (hc.chart y hy).mem i
      · exact one_mem _
    · split_ifs
      · exact intCast_mem _ _
      · exact zero_mem _
  · simp only [add_smul, Finset.sum_add_distrib, mul_smul, ← dK_eq_frame, ← Finset.smul_sum, ← hdu,
      ite_smul, zero_smul]
    rw [dlog_mul, dlog_prod, Finset.sum_ite_mem, Finset.univ_inter]
    congr 1
    · rw [dlog, Units.val_inv_eq_inv_val, hdu]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [dK_eq_frame x J j, ite_smul]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [dlog_zpow, frame, if_pos hj, Int.cast_smul_eq_zsmul]

theorem isComb_frame {Z : Set X} {U : X.Opens} {n : ℕ} {x : Fin n → X.functionFieldˣ} {J : Finset (Fin n)}
    (hc : IsLogChart Z U x J) {y : X} (hy : y ∈ U) (i : Fin n) :
    IsComb (locRing y) (dlog '' {g | LogUnit Z y g}) (frame x J i) := by
  have hlog : ∀ w : X.functionFieldˣ, UnitAt y (w : X.functionField) → LogUnit Z y w := fun w hw =>
    (hc.logUnit y hy w).2 ⟨w, 0, hw, by simp⟩
  by_cases hi : i ∈ J
  · refine isComb_single (one_mem _) ⟨x i, (hc.logUnit y hy _).2 ⟨1, Pi.single i 1, ?_, ?_⟩, rfl⟩ ?_
    · rw [Units.val_one]; exact unitAt_one y
    · rw [one_mul, Finset.prod_eq_single_of_mem i hi (fun j _ hj => by simp [Pi.single_apply, hj])]
      simp
    · rw [frame, if_pos hi, one_smul]
  · have hm : RegAt y (x i : X.functionField) := (hc.chart y hy).mem i
    obtain ⟨s, hs⟩ := hm
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self s with h | h
    · have hu : UnitAt y (x i : X.functionField) := ⟨s, h, hs⟩
      refine isComb_single ((hc.chart y hy).mem i) ⟨x i, hlog _ hu, rfl⟩ ?_
      rw [frame, if_neg hi, smul_dlog]
    · have hu : UnitAt y (1 - (x i : X.functionField)) := ⟨1 - s, h, by rw [map_sub, map_one, hs]⟩
      refine isComb_single (c := -(1 - (x i : X.functionField)))
        (neg_mem (sub_mem (one_mem _) ((hc.chart y hy).mem i)))
        ⟨Units.mk0 _ hu.ne_zero, hlog _ hu, rfl⟩ ?_
      have h2 := smul_dlog (Units.mk0 _ hu.ne_zero)
      rw [Units.val_mk0] at h2
      rw [frame, if_neg hi, neg_smul, h2]
      simp [dK]

end Scheme

theorem logAt_eq_chartForms : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : Set X) (U : X.Opens) {n : ℕ}
    (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n)) (G : CartierDiv X) (y : X) (t : X.functionFieldˣ)
    (a : ℕ), IsLogChart Z U x J → y ∈ U → G.IsEqn y t → logAt Z G a y = chartForms (locRing y) x J t a := by
  intro X _ Z U n x J G y t a hc hy ht
  have hM : {c | G.RegularAt y c} = {c | c * (t : X.functionField) ∈ locRing y} :=
    Set.ext fun c => ht.regularAt_iff
  have hstab : ∀ c ∈ {c | c * (t : X.functionField) ∈ locRing y}, ∀ b ∈ locRing y,
      c * b ∈ {c | c * (t : X.functionField) ∈ locRing y} := fun c hc b hb => by
    simp only [Set.mem_setOf_eq] at hc ⊢
    rw [mul_right_comm]; exact mul_mem hc hb
  unfold logAt chartForms
  rw [hM]
  apply le_antisymm
  · exact spanForms_le_of_isComb _ a hstab fun v ⟨g, hg, e⟩ => e ▸ isComb_dlog hc hy hg
  · exact spanForms_le_of_isComb _ a hstab fun v ⟨i, e⟩ => e ▸ isComb_frame hc hy i

end GlobalTheory.LogDR.ChartStalk
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR

variable {X : Scheme.{0}} [IsIntegral X]

theorem latSec_map {V V' : Type} [AddCommGroup V] [AddCommGroup V'] (M : X → AddSubgroup V)
    (φ : V →+ V') (hφ : Function.Injective φ) (U : X.Opens) (h : genericPoint X ∈ U) :
    (latSec M U).map φ = latSec (fun y => (M y).map φ) U := by
  ext w
  simp only [latSec, AddSubgroup.mem_map, AddSubgroup.mem_iInf]
  constructor
  · rintro ⟨v, hv, rfl⟩ y hy
    exact ⟨v, hv y hy, rfl⟩
  · intro hw
    obtain ⟨v, -, hv⟩ := hw _ h
    refine ⟨v, fun y hy => ?_, hv⟩
    obtain ⟨u, hu, hu'⟩ := hw y hy
    rwa [hφ (hu'.trans hv.symm)] at hu

def LatModel.mapLin {V V' : Type} [AddCommGroup V] [Module X.functionField V] [AddCommGroup V']
    [Module X.functionField V'] {M : X → AddSubgroup V} {F : X.Modules} (L : LatModel M F)
    (φ : V →ₗ[X.functionField] V') (hφ : Function.Injective φ) :
    LatModel (fun y => (M y).map φ.toAddMonoidHom) F where
  val U h := φ.toAddMonoidHom.comp (L.val U h)
  inj U h := hφ.comp (L.inj U h)
  range U h := by
    rw [AddMonoidHom.range_comp, L.range U h]
    exact latSec_map M φ.toAddMonoidHom hφ U h
  res U W e h s := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, L.res U W e h s]
  smul U h r s := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, L.smul U h r s, LinearMap.toAddMonoidHom_coe,
      LinearMap.map_smul]

def LatModel.transfer {V : Type} [AddCommGroup V] [Module X.functionField V] {M : X → AddSubgroup V}
    {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') (U : X.Opens) (h : genericPoint X ∈ U)
    (s : Γ(F, U)) : Γ(F', U) :=
  Classical.choose (show L.val U h s ∈ (L'.val U h).range by
    rw [L'.range U h, ← L.range U h]; exact ⟨s, rfl⟩)

theorem LatModel.val_transfer {V : Type} [AddCommGroup V] [Module X.functionField V]
    {M : X → AddSubgroup V} {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') (U : X.Opens)
    (h : genericPoint X ∈ U) (s : Γ(F, U)) : L'.val U h (L.transfer L' U h s) = L.val U h s :=
  Classical.choose_spec (show L.val U h s ∈ (L'.val U h).range by
    rw [L'.range U h, ← L.range U h]; exact ⟨s, rfl⟩)

def LatModel.secEquiv {V : Type} [AddCommGroup V] [Module X.functionField V] {M : X → AddSubgroup V}
    {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') (U : X.Opens) (h : genericPoint X ∈ U) :
    Γ(F, U) ≃ₗ[Γ(X, U)] Γ(F', U) where
  toFun := L.transfer L' U h
  map_add' s t := L'.inj U h (by simp only [map_add (f := _), LatModel.val_transfer])
  map_smul' r s := L'.inj U h (by
    simp only [RingHom.id_apply, LatModel.val_transfer, L'.smul U h, L.smul U h])
  invFun := L'.transfer L U h
  left_inv s := L.inj U h (by simp only [LatModel.val_transfer])
  right_inv s := L'.inj U h (by simp only [LatModel.val_transfer])

theorem LatModel.val_secEquiv {V : Type} [AddCommGroup V] [Module X.functionField V]
    {M : X → AddSubgroup V} {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') (U : X.Opens)
    (h : genericPoint X ∈ U) (s : Γ(F, U)) : L'.val U h (L.secEquiv L' U h s) = L.val U h s :=
  L.val_transfer L' U h s

theorem subsingleton_sec_of_not_gen (F : X.Modules) {U : X.Opens} (hU : genericPoint X ∉ U) :
    Subsingleton Γ(F, U) := by
  haveI : Subsingleton Γ(X, U) := ⟨fun a b => fn_ext fun h => absurd h hU⟩
  exact Module.subsingleton Γ(X, U) Γ(F, U)


open Classical in
def LatModel.secEquiv' {V : Type} [AddCommGroup V] [Module X.functionField V] {M : X → AddSubgroup V}
    {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') (U : X.Opens) :
    Γ(F, U) ≃ₗ[Γ(X, U)] Γ(F', U) :=
  if h : genericPoint X ∈ U then L.secEquiv L' U h else
    haveI := subsingleton_sec_of_not_gen F h
    haveI := subsingleton_sec_of_not_gen F' h
    LinearEquiv.ofSubsingleton _ _

def LatModel.iso {V : Type} [AddCommGroup V] [Module X.functionField V] {M : X → AddSubgroup V}
    {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') : F ≅ F' :=
  GlobalTheory.LB.isoOfLinear (L.secEquiv' L') fun {U W} e s => by
    by_cases hW : genericPoint X ∈ W
    · have hU : genericPoint X ∈ U := e hW
      apply L'.inj W hW
      simp only [LatModel.secEquiv', dif_pos hW, dif_pos hU]
      rw [L.val_secEquiv L' W hW, L'.res U W e hW, L.res U W e hW, L.val_secEquiv L' U hU]
    · haveI := subsingleton_sec_of_not_gen F' hW
      exact Subsingleton.elim _ _

theorem latModel_map_and_unique : ∀ (X : Scheme.{0}) [IsIntegral X] {V V' : Type} [AddCommGroup V] [Module X.functionField V] [AddCommGroup V'] [Module X.functionField V'] (M : X → AddSubgroup V) (F F' : X.Modules) (φ : V →ₗ[X.functionField] V'), Function.Injective φ → LatModel M F → (Nonempty (LatModel (fun y => (M y).map φ.toAddMonoidHom) F)) ∧ (LatModel M F' → Nonempty (F ≅ F')) := by
  intro X _ V V' _ _ _ _ M F F' φ hφ L
  exact ⟨⟨L.mapLin φ hφ⟩, fun L' => ⟨L.iso L'⟩⟩

end GlobalTheory.LogDR
end
end

section

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem LogDR.round_coeff_mem : ∀ (K : Type) [Field K] (p : ℕ) (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (I J : Finset (Fin n)) (t : Kˣ) (r : Fin n → ℕ) (g : K), 0 < p → AlgChart A x → (∀ j, r j < p) → g ^ p * ((t ^ p * ∏ j ∈ J, x j ^ r j : Kˣ) : K) / ∏ j ∈ I \ J, (x j : K) ∈ A → g * t / ∏ j ∈ I \ J, (x j : K) ∈ A := by
  intro K _ p A n x I J t r g hp hA hr h
  have hP0 : (∏ j ∈ I \ J, (x j : K)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => (x j).ne_zero)
  have hQ0 : (∏ j ∈ J, (x j : K)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => (x j).ne_zero)
  have hcast : ((t ^ p * ∏ j ∈ J, x j ^ r j : Kˣ) : K) = (t : K) ^ p * ∏ j ∈ J, (x j : K) ^ (r j) := by
    push_cast; rfl
  rw [hcast] at h
  have hpow : ∀ j ∈ J, (x j : K) ^ p = (x j : K) ^ (r j) * (x j : K) * (x j : K) ^ (p - 1 - r j) := by
    intro j _
    rw [← pow_succ, ← pow_add]
    congr 1
    have := hr j
    omega
  have hprod : (∏ j ∈ J, (x j : K)) ^ p = (∏ j ∈ J, (x j : K) ^ (r j)) * (∏ j ∈ J, (x j : K)) *
      ∏ j ∈ J, (x j : K) ^ (p - 1 - r j) := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl hpow
  have hS : ∏ j ∈ J ∪ I \ J, (x j : K) = (∏ j ∈ J, (x j : K)) * ∏ j ∈ I \ J, (x j : K) :=
    Finset.prod_union Finset.disjoint_sdiff
  have hB : ∏ j ∈ J, (x j : K) ^ (p - 1 - r j) ∈ A :=
    Subring.prod_mem _ (fun j _ => Subring.pow_mem _ (hA.mem j) _)
  have key : (g * t * ∏ j ∈ J, (x j : K)) ^ p / ∏ j ∈ J ∪ I \ J, (x j : K) =
      (g ^ p * ((t : K) ^ p * ∏ j ∈ J, (x j : K) ^ (r j)) / ∏ j ∈ I \ J, (x j : K)) *
        ∏ j ∈ J, (x j : K) ^ (p - 1 - r j) := by
    rw [hS, mul_pow, mul_pow, hprod]
    field_simp
  have h2 := hA.root (J ∪ I \ J) _ p hp (key ▸ A.mul_mem h hB)
  have e : (g * t * ∏ j ∈ J, (x j : K)) / ∏ j ∈ J ∪ I \ J, (x j : K) = g * t / ∏ j ∈ I \ J, (x j : K) := by
    rw [hS]
    field_simp
  rwa [e] at h2

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

namespace GlobalTheory.LogDR

theorem logAt_smul_mem : ∀ (X : Scheme.{0}) [IsIntegral X] (Z : Set X) (G : CartierDiv X) (a : ℕ) (y : X)
    (f : X.functionField) (η : abelian₂ X.functionField), RegAt y f → η ∈ logAt Z G a y → f • η ∈ logAt Z G a y := by
  intro X _ Z G a y f η hf hη
  unfold logAt spanForms at hη ⊢
  induction hη using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    refine ⟨f * c, ?_, v, hv, ?_⟩
    · exact (show G.RegularAt y c from hc).regAt_mul hf
    · rw [smul_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

end GlobalTheory.LogDR
end
