module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle002
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
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem isTangent_of_isLieComb {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ} {cv : Fin n → R}
    {v : Fin n → (epsR R ⟶ G)} {w : epsR R ⟶ G} (hv : ∀ i, IsTangent (v i)) (h : IsLieComb cv v w) :
    IsTangent w := by
  rw [(Chart.isLieComb_iff cv v w).1 h, ← Chart.isTan_iff]
  refine List.prod_induction Chart.IsTan (fun a b ha hb => Chart.isTan_mul ha hb) Chart.isTan_one ?_
  intro a ha
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 ha
  exact Chart.isTan_scale (cv i) ((Chart.isTan_iff _).2 (hv i))

theorem vec_bijective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), (∀ cv, ∃! w, Λ.Vec cv w) ∧ (∀ cv w, Λ.Vec cv w → IsTanAt x w) ∧ ∀ w, IsTanAt x w → ∃! cv, Λ.Vec cv w := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ
  obtain ⟨v, hv, hb, -⟩ := M.lie R f Λ.t' Λ.m2
  have key : ∀ cv w, Λ.Vec cv w ↔ ∃ u', IsLieComb cv v u' ∧ u'.left ≫ Λ.m1.φ = w := by
    intro cv w
    constructor
    · rintro ⟨v', u', h1, h2, h3⟩
      have e : v' = v := funext fun j => Chart.inj_over Λ.m2.cart ((h1 j).trans (hv j).symm)
      exact ⟨u', e ▸ h2, h3⟩
    · rintro ⟨u', h2, h3⟩
      exact ⟨v, u', hv, h2, h3⟩
  refine ⟨fun cv => ?_, fun cv w h => ?_, fun w hw => ?_⟩
  · refine ⟨(Chart.prodPts cv v).left ≫ Λ.m1.φ, (key _ _).2 ⟨_, (Chart.isLieComb_iff cv v _).2 rfl, rfl⟩, ?_⟩
    intro w hw
    obtain ⟨u', h2, h3⟩ := (key _ _).1 hw
    rw [← h3, (Chart.isLieComb_iff cv v _).1 h2]
  · obtain ⟨u', h2, rfl⟩ := (key _ _).1 h
    refine ⟨?_, (Chart.tan_push Λ.m1.cart u').1 (isTangent_of_isLieComb hb.1 h2)⟩
    have e1 : Λ.m1.φ ≫ Xo.univ.t.G.hom = Λ.t'.G.hom ≫ x := Λ.m1.cart.1.w
    have e2 : u'.left ≫ Λ.t'.G.hom = spMap (algebraMap R (DualNumber R)) := Over.w u'
    rw [Category.assoc, e1, ← Category.assoc, e2]
  · let u' : epsR R ⟶ Λ.t'.G :=
      Over.homMk (Λ.m1.cart.1.lift w (spMap (algebraMap R (DualNumber R))) hw.1) (Λ.m1.cart.1.lift_snd _ _ _)
    have hu : u'.left ≫ Λ.m1.φ = w := Λ.m1.cart.1.lift_fst _ _ _
    have ht : IsTangent u' := (Chart.tan_push Λ.m1.cart u').2 (by
      have := hw.2
      rw [← hu] at this
      exact this)
    obtain ⟨cv, hc, huniq⟩ := hb.2 u' ht
    refine ⟨cv, (key _ _).2 ⟨u', hc, hu⟩, fun cv' h' => ?_⟩
    obtain ⟨u'', h2, h3⟩ := (key _ _).1 h'
    have e : u'' = u' := Chart.inj_over Λ.m1.cart (h3.trans hu.symm)
    exact huniq cv' (e ▸ h2)

end GlobalTheory.Reg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

noncomputable section

namespace GlobalTheory.Reg.VecEig

open GlobalTheory.GrpTangent

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def comb {n : ℕ} (v : Fin n → (epsR R ⟶ G)) (c : Fin n → R) : epsR R ⟶ G :=
  ∏ i, epsScale (c i) ≫ v i

theorem isLieComb_iff_comb {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = comb v c := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    apply Over.OverMorphism.ext
    rw [hu i, Over.comp_left]
    rfl
  · rintro rfl
    refine ⟨fun i => epsScale (c i) ≫ v i, fun i => ?_, ?_⟩
    · rw [Over.comp_left]
      rfl
    · rw [List.prod_ofFn]
      rfl

theorem comp_finProd {X Y : Over (Sp R)} (g : X ⟶ Y) {κ : Type} (s : Finset κ) (u : κ → (Y ⟶ G)) :
    g ≫ ∏ i ∈ s, u i = ∏ i ∈ s, g ≫ u i := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty]
    exact Chart.comp_one' g
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, comp_mul, ih]

theorem finProd_comp {X : Over (Sp R)} (g : G ⟶ G) [IsMonHom g] {κ : Type} (s : Finset κ) (u : κ → (X ⟶ G)) :
    (∏ i ∈ s, u i) ≫ g = ∏ i ∈ s, u i ≫ g := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty]
    exact one_comp g
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, mul_comp, ih]

theorem epsScale_sum_comp {w : epsR R ⟶ G} (hw : IsTangent w) {κ : Type} (s : Finset κ) (a : κ → R) :
    epsScale (∑ i ∈ s, a i) ≫ w = ∏ i ∈ s, epsScale (a i) ≫ w := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.prod_empty]
    exact epsScale_zero_comp hw
  · intro b t hb ih
    rw [Finset.sum_insert hb, Finset.prod_insert hb, epsScale_add_comp _ _ hw, ih]

theorem epsScale_comb {n : ℕ} (v : Fin n → (epsR R ⟶ G)) (c : Fin n → R) (z : R) :
    epsScale z ≫ comb v c = comb v (z • c) := by
  unfold comb
  rw [comp_finProd]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Category.assoc, epsScale_mul, Pi.smul_apply, smul_eq_mul]

theorem comb_comp {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (g : G ⟶ G) [IsMonHom g]
    (A : Matrix (Fin n) (Fin n) R) (hA : ∀ j, v j ≫ g = comb v fun i => A i j) (c : Fin n → R) :
    comb v c ≫ g = comb v (A.mulVec c) := by
  calc comb v c ≫ g = ∏ j, (epsScale (c j) ≫ v j) ≫ g := finProd_comp g _ _
    _ = ∏ j, comb v (c j • fun i => A i j) :=
        Finset.prod_congr rfl fun j _ => by rw [Category.assoc, hA j, epsScale_comb]
    _ = ∏ j, ∏ i, epsScale (A i j * c j) ≫ v i := Finset.prod_congr rfl fun j _ => by
        unfold comb
        exact Finset.prod_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_comm (c j)]
    _ = ∏ i, ∏ j, epsScale (A i j * c j) ≫ v i := Finset.prod_comm
    _ = comb v (A.mulVec c) := by
        unfold comb
        exact Finset.prod_congr rfl fun i _ => (epsScale_sum_comp (hv i) Finset.univ fun j => A i j * c j).symm

theorem isTangent_comb {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (c : Fin n → R) :
    IsTangent (comb v c) := by
  rw [isTangent_iff]
  unfold comb
  rw [comp_finProd]
  exact Finset.prod_eq_one fun i _ => (isTangent_iff _).1 (isTangent_epsScale (c i) (hv i))

theorem comb_injective {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) : Function.Injective (comb v) := by
  intro c d h
  have hc : IsLieComb c v (comb v c) := (isLieComb_iff_comb c v (comb v c)).2 rfl
  have hd : IsLieComb d v (comb v c) := (isLieComb_iff_comb d v (comb v c)).2 h
  exact (hv.2 _ (isTangent_comb hv.1 c)).unique hc hd

theorem pt_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) {X : Over S'} {u u' : X ⟶ t'.G}
    (h : u.left ≫ m.φ = u'.left ≫ m.φ) : u = u' := by
  cases m with
  | mk cm cart base act lin =>
    apply Over.OverMorphism.ext
    refine cart.1.hom_ext h ?_
    rw [Over.w u, Over.w u']

end GlobalTheory.Reg.VecEig


open GlobalTheory.Reg.VecEig GlobalTheory.GrpTangent in
theorem GlobalTheory.Reg.isEigAt_iff_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ (τ : E →+* ℂ) (cv : Fin M.n → R) (w : Sp (DualNumber R) ⟶ Xo.univ.t.G.left), Λ.Vec cv w → (IsEigAt c τ w ↔ M.Eig f τ cv) := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ τ cv w hw
  obtain ⟨v', u', hv', hu', rfl⟩ := hw
  obtain ⟨v, hv0, hvb, hρ⟩ := M.lie R f Λ.t' Λ.m2
  obtain rfl : v' = v := funext fun j => pt_ext Λ.m2 ((hv' j).trans (hv0 j).symm)
  have hu := (isLieComb_iff_comb _ _ _).1 hu'
  have hA := fun a j => (isLieComb_iff_comb _ _ _).1 (hρ a j)
  unfold IsEigAt MChart.Eig
  refine forall_congr' fun a => ?_
  have : IsMonHom (Λ.t'.act.act a) := Λ.t'.act.hom a
  have e1 : (u'.left ≫ Λ.m1.φ) ≫ (Xo.univ.t.act.act a).left = (u' ≫ Λ.t'.act.act a).left ≫ Λ.m1.φ := by
    rw [Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg (u'.left ≫ ·) (Λ.m1.act a).symm
  have e2 : spMap (epsMul (algebraMap c.F R (embK c τ a))) ≫ u'.left ≫ Λ.m1.φ =
      (epsScale (algebraMap c.F R (embK c τ a)) ≫ u').left ≫ Λ.m1.φ := by
    rw [Over.comp_left, Category.assoc]
    rfl
  rw [e1, e2, hu, comb_comp hvb.1 _ ((M.ρ a).map f) (hA a), epsScale_comb]
  constructor
  · intro h
    exact comb_injective hvb (pt_ext Λ.m1 h)
  · intro h
    rw [h]
end
end

section

open NumberField

namespace GlobalTheory.Reg.CellChart

section Lin
open Matrix

theorem det_of_inCell {R : Type} [CommRing R] {n r : ℕ} (ix : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) R)
    (h : InCell ix u) : (u.submatrix ix id).det = 1 := by
  rw [Matrix.det_of_lowerTriangular (u.submatrix ix id) (fun i j hij => h.1 i j hij)]
  simp [h.2]

theorem rank_of_quasi_idem {L : Type} [Field L] {n : ℕ} (P : Matrix (Fin n) (Fin n) L) (N : L) (hN : N ≠ 0)
    (hP : P * P = N • P) (S : Submodule L (Fin n → L)) (hS : ∀ x, x ∈ S ↔ P.mulVec x = N • x) :
    P.rank = Module.finrank L S := by
  have : LinearMap.range P.mulVecLin = S := by
    ext x
    rw [hS, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP, Matrix.smul_mulVec]
    · intro h
      refine ⟨N⁻¹ • x, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_smul, h, smul_smul, inv_mul_cancel₀ hN, one_smul]
  rw [← Matrix.finrank_range_mulVecLin, this]

theorem exists_minor {L : Type} [Field L] {n r : ℕ} (P : Matrix (Fin n) (Fin n) L) (N : L) (hN : N ≠ 0)
    (ix : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) L) (hu : P * u = N • u) (hc : InCell ix u) :
    ∃ κ : Fin r → Fin n, (P.submatrix ix κ).det ≠ 0 := by
  have h : P.submatrix ix id * u = N • u.submatrix ix id := by
    ext i j
    have := congrFun (congrFun hu (ix i)) j
    simpa [Matrix.mul_apply] using this
  obtain ⟨κ, hκ⟩ := GlobalTheory.exists_cols_det_ne_zero_of_mul (P.submatrix ix id) u (by
    rw [h, Matrix.det_smul, det_of_inCell ix u hc]; simp [hN])
  exact ⟨κ, hκ⟩

theorem eq_of_rows {L : Type} [Field L] {n r m : ℕ} (P : Matrix (Fin n) (Fin n) L) (hr : P.rank = r) (N : L)
    (hN : N ≠ 0) (ix κ : Fin r → Fin n) (hd : (P.submatrix ix κ).det ≠ 0) (u : Matrix (Fin n) (Fin m) L)
    (hu : P * u = N • u) : u = P.submatrix id κ * (P.submatrix ix κ)⁻¹ * u.submatrix ix id := by
  have h : P.submatrix ix id * u = N • u.submatrix ix id := by
    ext i j
    have := congrFun (congrFun hu (ix i)) j
    simpa [Matrix.mul_apply] using this
  have h1 := ((GlobalTheory.rank_minor_factorisation L n r P hr ix).1 κ hd)
  have h2 : N • u = N • (P.submatrix id κ * (P.submatrix ix κ)⁻¹ * u.submatrix ix id) := by
    rw [← hu, ← Matrix.mul_smul, ← h, ← Matrix.mul_assoc, ← h1]
  exact smul_right_injective _ hN h2

end Lin

theorem exists_projector (E K : Type) [Field E] [NumberField E] [Field K] (emb : (E →+* ℂ) → (E →+* K))
    (hemb : Function.Injective emb) (O : Type) [CommRing O] [IsDomain O] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] (α : O →+* A) (n : ℕ) (ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) A) (τ : E →+* ℂ) :
    ∃ (N : O) (p : Matrix (Fin n) (Fin n) A), N ≠ 0 ∧ ∀ (R : Type) [CommRing R] [Algebra K R] (f : A →+* R),
      f.comp α = (algebraMap K R).comp (algebraMap O K) →
      (p.map f * p.map f = f (α N) • p.map f) ∧ ∀ x : Fin n → R,
        (∀ b : 𝓞 E, ((ρ b).map f).mulVec x = algebraMap K R (emb τ (b : E)) • x) ↔
          (p.map f).mulVec x = f (α N) • x := by
  obtain ⟨m, a, κ, h⟩ := GlobalTheory.exists_eigen_projector_ringOfIntegers E K emb hemb τ
  obtain ⟨N, hN⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) κ
  choose t ht using hN
  refine ⟨N, ∑ k, α (t k) • ρ (a k), nonZeroDivisors.ne_zero N.2, fun R _ _ f hf => ?_⟩
  have hf' : ∀ o, f (α o) = algebraMap K R (algebraMap O K o) := fun o => RingHom.congr_fun hf o
  obtain ⟨h1, h2⟩ := h R n (f.mapMatrix.comp ρ)
  set π := ∑ k, algebraMap K R (κ k) • (f.mapMatrix.comp ρ) (a k) with hπ
  have hp : (∑ k, α (t k) • ρ (a k)).map f = f (α N) • π := by
    ext i j
    have ht' : ∀ i, algebraMap O K (t i) = algebraMap O K N * κ i := fun i => (ht i).trans (Algebra.smul_def _ _)

    simp only [hπ, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, hf', ht',
    Finset.mul_sum, RingHom.comp_apply, RingHom.mapMatrix_apply, mul_assoc]
  have hu : IsUnit (f (α N)) := by
    rw [hf']
    exact (IsLocalization.map_units K N).map _
  have hππ : π * π = π := by
    ext i j
    have := h2 (fun k => π k j) (fun b => by
      funext k
      have := congrFun (congrFun (h1 b) k) j
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this)
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun this i
  rw [hp]
  refine ⟨by rw [Matrix.smul_mul, Matrix.mul_smul, hππ], fun x => ⟨fun hx => ?_, fun hx b => ?_⟩⟩
  · rw [Matrix.smul_mulVec, h2 x hx]
  · rw [Matrix.smul_mulVec] at hx
    have hx' : π.mulVec x = x := hu.smul_left_cancel.mp hx
    have := congrArg (fun M => Matrix.mulVec M x) (h1 b)
    simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, hx'] at this
    exact this

theorem loc_descr {K O A F : Type} [Field K] [CommRing O] [IsDomain O] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Field F] [Algebra K F] (α : O →+* A) (i : A →+* F)
    (hi : i.comp α = (algebraMap K F).comp (algebraMap O K)) (g : A) (hg : i g ≠ 0) (x : F)
    (hx : x ∈ Algebra.adjoin K (insert (i g)⁻¹ (Set.range i))) :
    ∃ (a : A) (b : O) (m : ℕ), b ≠ 0 ∧ x * i (α b * g ^ m) = i a := by
  have hi' : ∀ o, i (α o) = algebraMap K F (algebraMap O K o) := fun o => RingHom.congr_fun hi o
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨a, rfl⟩
    · exact ⟨1, 1, 1, one_ne_zero, by simp [hg]⟩
    · exact ⟨a, 1, 0, one_ne_zero, by simp⟩
  | algebraMap k =>
    obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors O) k
    refine ⟨α a, b, 0, nonZeroDivisors.ne_zero b.2, ?_⟩
    rw [pow_zero, mul_one, hi', hi', ← map_mul, h]
  | add x y _ _ hx hy =>
    obtain ⟨a, b, m, hb, h⟩ := hx
    obtain ⟨a', b', m', hb', h'⟩ := hy
    refine ⟨a * (α b' * g ^ m') + a' * (α b * g ^ m), b * b', m + m', mul_ne_zero hb hb', ?_⟩
    simp only [map_add (f := _), map_mul, map_pow] at h h' ⊢
    rw [← h, ← h']; ring
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, m, hb, h⟩ := hx
    obtain ⟨a', b', m', hb', h'⟩ := hy
    refine ⟨a * a', b * b', m + m', mul_ne_zero hb hb', ?_⟩
    simp only [map_add (f := _), map_mul, map_pow] at h h' ⊢
    rw [← h, ← h']; ring

theorem loc_lift {K O A F L : Type} [Field K] [CommRing O] [IsDomain O] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Field F] [Algebra K F] [Field L] [Algebra K L] (α : O →+* A) (i : A →+* F)
    (hinj : Function.Injective i)
    (hi : i.comp α = (algebraMap K F).comp (algebraMap O K)) (g : A) (hg : i g ≠ 0) (f : A →+* L)
    (hf : f.comp α = (algebraMap K L).comp (algebraMap O K)) (hfg : f g ≠ 0) :
    ∃ ψ : Algebra.adjoin K (insert (i g)⁻¹ (Set.range i)) →ₐ[K] L,
      ∀ a (h : i a ∈ Algebra.adjoin K (insert (i g)⁻¹ (Set.range i))), ψ ⟨i a, h⟩ = f a := by
  have hi' : ∀ o, i (α o) = algebraMap K F (algebraMap O K o) := fun o => RingHom.congr_fun hi o
  have hf' : ∀ o, f (α o) = algebraMap K L (algebraMap O K o) := fun o => RingHom.congr_fun hf o
  set R₀ := Algebra.adjoin K (insert (i g)⁻¹ (Set.range i)) with hR₀
  have hm : ∀ a, i a ∈ R₀ := fun a => Algebra.subset_adjoin (Or.inr ⟨a, rfl⟩)
  let i₀ : A →+* R₀ := i.codRestrict R₀.toSubring hm
  letI : Algebra A R₀ := i₀.toAlgebra
  let S : Submonoid A := (IsUnit.submonoid R₀).comap i₀ ⊓ (IsUnit.submonoid L).comap f
  have hO : ∀ b : O, i₀ (α b) = algebraMap K R₀ (algebraMap O K b) := fun b => Subtype.ext (hi' b)
  have hK : ∀ b : O, b ≠ 0 → IsUnit (algebraMap O K b) := fun b hb =>
    IsLocalization.map_units K (⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩ : nonZeroDivisors O)
  have hgS : g ∈ S := ⟨IsUnit.of_mul_eq_one (⟨(i g)⁻¹, Algebra.subset_adjoin (Or.inl rfl)⟩ : R₀)
    (Subtype.ext (mul_inv_cancel₀ hg)), isUnit_iff_ne_zero.mpr hfg⟩
  have hbS : ∀ b : O, b ≠ 0 → α b ∈ S := fun b hb =>
    ⟨show IsUnit (i₀ (α b)) from hO b ▸ (hK b hb).map _, show IsUnit (f (α b)) from hf' b ▸ (hK b hb).map _⟩
  haveI : IsLocalization S R₀ := by
    refine (isLocalization_iff S R₀).mpr ⟨fun y => y.2.1, fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
    · obtain ⟨a, b, m, hb, h⟩ := loc_descr α i hi g hg z z.2
      exact ⟨⟨a, ⟨α b * g ^ m, S.mul_mem (hbS b hb) (S.pow_mem hgS m)⟩⟩, Subtype.ext h⟩
    · rw [hinj (congrArg Subtype.val h)]
  let φ : R₀ →+* L := IsLocalization.lift (M := S) (g := f) (fun y => y.2.2)
  have hφ : ∀ a, φ (i₀ a) = f a := fun a => IsLocalization.lift_eq (M := S) (g := f) (fun y => y.2.2) a
  have hc : φ.comp (algebraMap K R₀) = algebraMap K L := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors O) (RingHom.ext fun o => ?_)
    simp only [RingHom.comp_apply]
    rw [← hO, hφ, hf']
  exact ⟨⟨φ, fun k => RingHom.congr_fun hc k⟩, fun a h => hφ a⟩

end GlobalTheory.Reg.CellChart
end
