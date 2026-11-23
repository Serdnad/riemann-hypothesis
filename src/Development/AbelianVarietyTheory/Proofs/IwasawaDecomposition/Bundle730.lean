module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle669
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle717
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim

namespace GlobalTheory.PolFan.CarDim

section Descend

variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X]

theorem exists_pull_mkQ_eq_of_vanish (K : Submodule O X) (f : LinearMap.BilinForm ℤ X)
    (h1 : ∀ x ∈ K, ∀ y, f x y = 0) (h2 : ∀ x, ∀ y ∈ K, f x y = 0) :
    ∃ δ : LinearMap.BilinForm ℤ (X ⧸ K), pull K.mkQ δ = f := by
  let e := Submodule.Quotient.restrictScalarsEquiv ℤ K
  let g := LinearMap.liftQ₂ (K.restrictScalars ℤ) (K.restrictScalars ℤ) f
    (fun x hx => LinearMap.ext fun y => h1 x hx y) (fun y hy => LinearMap.ext fun x => h2 x y hy)
  refine ⟨g.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap, LinearMap.ext₂ fun a b => ?_⟩
  simp [pull_apply, e, g]
  rfl

end Descend

theorem exists_cell_quot_orad_of_inRCone : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ : InvFun (𝓞 E))
    (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X],
    (∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
      IsCell H.bar ψ γ → IsFaceCut γ s h → IsCell H.bar ψ (fun i => γ (s i))) →
    ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ →
      InRCone γ β → ∃ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ (X ⧸ (orad β : Submodule (𝓞 E) X))),
        IsCell H.bar ψ δ ∧ InRCone (fun i => pull (orad β : Submodule (𝓞 E) X).mkQ (δ i)) β ∧ genRank δ ≤ genRank γ := by
  intro E _ _ _ H ψ X _ _ _ hface β hβ hβp m γ hγ hβγ
  classical
  set K : Submodule (𝓞 E) X := orad β with hK
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian (K.restrictScalars ℤ) : (K.restrictScalars ℤ).FG)
  have hTK : ∀ k ∈ T, k ∈ K := fun k hk => by
    have : k ∈ K.restrictScalars ℤ := hT ▸ Submodule.subset_span hk
    exact this
  let hl : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := ∑ k ∈ T, LinearMap.applyₗ k ∘ₗ LinearMap.applyₗ k
  have hl_apply : ∀ β', hl β' = ∑ k ∈ T, β' k k := fun β' => by simp [hl]
  have hsym : ∀ i y z, γ i y z = γ i z y := fun i => (hγ.mem i).1
  have hvan : ∀ i, hl (γ i) = 0 ↔ ∀ x ∈ K, ∀ y, γ i x y = 0 := by
    intro i
    rw [hl_apply]
    constructor
    · intro h0
      have hkk : ∀ k ∈ T, γ i k k = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hγ.nonneg i k).1 h0
      have hle : K.restrictScalars ℤ ≤ LinearMap.ker (γ i) := by
        rw [← hT, Submodule.span_le]
        intro k hk
        exact LinearMap.ext fun w => ConeSub.eq_zero_of_self_eq_zero (γ i) (hsym i) (hγ.nonneg i) (hkk k hk) w
      intro x hx y
      have := hle hx
      rw [LinearMap.mem_ker] at this
      rw [this]; rfl
    · intro h0
      exact Finset.sum_eq_zero fun k hk => h0 k (hTK k hk) k
  have hnn : ∀ i, 0 ≤ hl (γ i) := fun i => by
    rw [hl_apply]; exact Finset.sum_nonneg fun k _ => hγ.nonneg i k
  set S : Finset (Fin m) := Finset.univ.filter fun i => hl (γ i) = 0 with hS
  let s : Fin S.card ↪ Fin m := (S.orderEmbOfFin rfl).toEmbedding
  have hs : Set.range s = ↑S := Finset.range_orderEmbOfFin S rfl
  have hcut : IsFaceCut γ s hl := ⟨hnn, fun j => by
    rw [hs]; simp [hS]⟩
  have hcell := hface m S.card γ s hl hγ hcut
  have hdesc : ∀ i : Fin S.card, ∃ δ : LinearMap.BilinForm ℤ (X ⧸ K), pull K.mkQ δ = γ (s i) := by
    intro i
    have hi : hl (γ (s i)) = 0 := by
      have : s i ∈ (S : Set (Fin m)) := hs ▸ Set.mem_range_self i
      simpa [hS] using this
    have h1 := (hvan (s i)).1 hi
    exact exists_pull_mkQ_eq_of_vanish K _ h1 fun x y hy => by rw [hsym]; exact h1 y hy x
  choose δ hδ using hdesc
  have hδ' : (fun i => pull K.mkQ (δ i)) = fun i => γ (s i) := funext hδ
  have hsurj : Function.Surjective K.mkQ := K.mkQ_surjective
  refine ⟨S.card, δ, ?_, ?_, ?_⟩
  · refine ⟨fun i => ?_, fun i y => ?_, ?_, ?_⟩
    · have hm := hcell.mem i
      rw [← hδ i] at hm
      refine ⟨fun y z => ?_, fun a y z => ?_⟩
      · obtain ⟨y, rfl⟩ := hsurj y
        obtain ⟨z, rfl⟩ := hsurj z
        exact hm.1 y z
      · obtain ⟨y, rfl⟩ := hsurj y
        obtain ⟨z, rfl⟩ := hsurj z
        have := hm.2 a y z
        simpa [pull_apply, map_smul] using this
    · obtain ⟨y, rfl⟩ := hsurj y
      have := hcell.nonneg i y
      rw [← hδ i] at this
      exact this
    · rw [← linearOn_pull_iff hsurj, hδ']
      exact hcell.linear
    · apply IsStrict.of_pull hsurj
      rw [hδ']
      exact hcell.strict
  · rw [hδ']
    obtain ⟨c, hc0, hc⟩ := hβγ
    have hzero : ∀ j, j ∉ S → c j = 0 := by
      intro j hj
      have hj' : hl (γ j) ≠ 0 := by simpa [hS] using hj
      rw [hl_apply] at hj'
      obtain ⟨k, hkT, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj'
      have hk := LinearMap.congr_fun₂ hc k k
      simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hk
      have hb : β k k = 0 := by
        have := (mem_orad.1 (hTK k hkT)) 1 k
        simpa using this
      rw [hb, Int.cast_zero] at hk
      have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        mul_nonneg (hc0 i) (Int.cast_nonneg (hγ.nonneg i k))).1 hk.symm j (Finset.mem_univ _)
      rcases mul_eq_zero.1 hall with h | h
      · exact h
      · exact absurd (Int.cast_eq_zero.1 h) hk0
    refine ⟨fun i => c (s i), fun i => hc0 _, ?_⟩
    rw [hc]
    exact (Fintype.sum_of_injective s s.injective (fun i => c (s i) • toReal (γ (s i))) (fun j => c j • toReal (γ j))
      (fun j hj => by
        rw [hzero j (by rw [hs] at hj; simpa using hj), zero_smul]) (fun i => rfl)).symm
  · rw [← genRank_pull hsurj δ, hδ']
    unfold genRank
    haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range γ)) := Module.Finite.span_of_finite ℤ (Set.finite_range γ)
    exact Submodule.finrank_mono (Submodule.span_mono (Set.range_comp_subset_range s γ))

end GlobalTheory.PolFan.CarDim
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

noncomputable section
namespace GlobalTheory.ChernPull

open ReciprocityTheory.L2DbarEstimates (V)
open ComplexConjugate

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

theorem conn_eq_sum (H : V n → Matrix r r ℂ) (z ζ : V n) :
    conn H z ζ = ∑ c, ζ c • conn H z (coordVec c) := by
  have hζ : ζ = ∑ c, ζ c • coordVec (n := n) c := by
    ext i; simp [coordVec, Pi.single_apply]
  conv_lhs => rw [hζ]
  have hl : ∀ (s : Finset (Fin n)), mdel H z (∑ c ∈ s, ζ c • coordVec c) = ∑ c ∈ s, ζ c • mdel H z (coordVec c) := by
    intro s
    induction s using Finset.induction_on with
    | empty => ext a b; simp
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, mdel_add_vec, mdel_smul_vec, ih]
  simp only [conn, hl, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.mul_sum, Matrix.mul_smul]

theorem curv_eq_sum (H : V n → Matrix r r ℂ) (z ξ ζ : V n) :
    curv H z ξ ζ = ∑ d, conj (ζ d) • curv H z ξ (coordVec d) := by
  have hζ : ζ = ∑ d, ζ d • coordVec (n := n) d := by
    ext i; simp [coordVec, Pi.single_apply]
  conv_lhs => rw [hζ]
  have hl : ∀ (s : Finset (Fin n)), mdbar (fun x => conn H x ξ) z (∑ d ∈ s, ζ d • coordVec d) =
      ∑ d ∈ s, conj (ζ d) • mdbar (fun x => conn H x ξ) z (coordVec d) := by
    intro s
    induction s using Finset.induction_on with
    | empty => ext a b; simp
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, mdbar_add_vec, mdbar_smul_vec, ih]
  simp only [curv, hl, Finset.sum_neg_distrib, smul_neg]

theorem mContDiffAt_conn {H : V n → Matrix r r ℂ} {y : V n} (h2 : MContDiffAt 2 H y)
    (hu : IsUnit (H y).det) (ξ : V n) : MContDiffAt 1 (fun x => conn H x ξ) y := by
  have h1 : MContDiffAt 1 H y := h2.of_le (by norm_num)
  have hu' : IsUnit ((H y)ᵀ).det := by rwa [Matrix.det_transpose]
  exact (h1.transpose.inv hu').mul ((h2.mdel (j := 1) (by norm_num) ξ).transpose)

theorem conn_comp_eventually {H : V n → Matrix r r ℂ} {φ : V n → V n} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (ξ : V n) :
    ∀ᶠ w in 𝓝 v, conn (fun x => H (φ x)) w ξ = ∑ c, (fderiv ℂ φ w ξ) c • conn H (φ w) (coordVec c) := by
  have hK : ∀ᶠ w in 𝓝 v, MContDiffAt 2 H (φ w) := hφ.continuousAt.eventually h2.eventually_two
  filter_upwards [hK, hφ.eventually_analyticAt] with w hw ha
  rw [← conn_eq_sum]
  have hm : mdel (fun x => H (φ x)) w ξ = mdel H (φ w) (fderiv ℂ φ w ξ) := by
    ext a b
    exact del_comp_holo (u := fun y => H y a b) ((hw a b).differentiableAt (by norm_num))
      ha.differentiableAt ξ
  simp only [conn, hm]

theorem curv_comp {H : V n → Matrix r r ℂ} {φ : V n → V n} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (hu : IsUnit (H (φ v)).det) (ξ η : V n) :
    curv (fun x => H (φ x)) v ξ η = ∑ c, (fderiv ℂ φ v ξ) c • curv H (φ v) (coordVec c) (fderiv ℂ φ v η) := by
  rw [curv, mdbar_congr (conn_comp_eventually hφ h2 ξ)]
  have hd : DifferentiableAt ℂ φ v := hφ.differentiableAt
  have hf : ∀ c : Fin n, DifferentiableAt ℂ (fun x => (fderiv ℂ φ x ξ) c) v := by
    intro c
    have h1 : DifferentiableAt ℂ (fun x => fderiv ℂ φ x ξ) v :=
      hφ.fderiv.differentiableAt.clm_apply (differentiableAt_const ξ)
    exact (EuclideanSpace.proj (𝕜 := ℂ) c).differentiableAt.comp v h1
  have hc : ∀ (c : Fin n) (i j : r), DifferentiableAt ℝ (fun y => conn H y (coordVec c) i j) (φ v) :=
    fun c i j => (mContDiffAt_conn h2 hu (coordVec c)).diff i j
  ext i j
  simp only [Matrix.neg_apply, mdbar_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_neg_distrib]
  rw [dbar_sum (A := fun c x => (fderiv ℂ φ x ξ) c * conn H (φ x) (coordVec c) i j) (fun c _ => ((hf c).restrictScalars ℝ).mul
    ((hc c i j).comp v (hd.restrictScalars ℝ)))]
  rw [ContinuousLinearMap.sum_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [dbar_mul (a := fun x => (fderiv ℂ φ x ξ) c) (b := fun x => conn H (φ x) (coordVec c) i j) ((hf c).restrictScalars ℝ) ((hc c i j).comp v (hd.restrictScalars ℝ)),
    dbar_eq_zero (hf c), dbar_comp_holo (u := fun y => conn H y (coordVec c) i j) (hc c i j) hd]
  simp [curv]

def substAlg (J : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
  aeval fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)

def jac (φ : V n → V n) (v : V n) : Matrix (Fin n) (Fin n) ℂ := fun c a => (fderiv ℂ φ v (coordVec a)) c

theorem curv_comp_coord {H : V n → Matrix r r ℂ} {φ : V n → V n} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (hu : IsUnit (H (φ v)).det) (a b : Fin n) :
    curv (fun x => H (φ x)) v (coordVec a) (coordVec b) =
      ∑ c, ∑ d, (jac φ v c a * conj (jac φ v d b)) • curv H (φ v) (coordVec c) (coordVec d) := by
  rw [curv_comp hφ h2 hu]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [curv_eq_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [smul_smul]; rfl

theorem curvPoly_comp {H : V n → Matrix r r ℂ} {φ : V n → V n} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (hu : IsUnit (H (φ v)).det) :
    curvPoly (fun x => H (φ x)) v = (curvPoly H (φ v)).map (substAlg (jac φ v)) := by
  refine Matrix.ext fun i j => ?_

  simp only [curvPoly, Matrix.of_apply, Matrix.map_apply, curv_comp_coord hφ h2 hu, Matrix.sum_apply,
  Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, substAlg, aeval_X, aeval_C, algebraMap_eq,
  Finset.sum_mul, Finset.mul_sum]
  simp_rw [← Fintype.sum_prod_type']
  let e : Fin n × Fin n × Fin n × Fin n ≃ Fin n × Fin n × Fin n × Fin n :=
    ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun _ => rfl, fun _ => rfl⟩
  exact Fintype.sum_equiv e _ _ fun x => by simp only [e, Equiv.coe_fn_mk]; ring

theorem charpolyRev_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {d : Type} [Fintype d]
    [DecidableEq d] (M : Matrix d d A) :
    (Matrix.charpolyRev M).map f = Matrix.charpolyRev (M.map f) := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 1
  by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

theorem chernPoly_comp {H : V n → Matrix r r ℂ} {φ : V n → V n} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (hu : IsUnit (H (φ v)).det) (k : ℕ) :
    chernPoly (fun x => H (φ x)) v k = substAlg (jac φ v) (chernPoly H (φ v) k) := by
  unfold chernPoly
  rw [curvPoly_comp hφ h2 hu]
  have hm : -(curvPoly H (φ v)).map (substAlg (jac φ v)) = (-curvPoly H (φ v)).map (substAlg (jac φ v)).toRingHom := by
    rw [Matrix.map_neg (f := (substAlg (jac φ v)).toRingHom) (fun a => map_neg _ a)]; rfl
  rw [hm, ← charpolyRev_map, Polynomial.coeff_map]
  rfl

theorem jac_eq_toMatrix (φ : V n → V n) (v : V n) :
    jac φ v = LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (fderiv ℂ φ v : V n →ₗ[ℂ] V n) := by
  ext c a
  simp [LinearMap.toMatrix_apply, jac, coordVec]

end GlobalTheory.ChernPull


open ReciprocityTheory.L2DbarEstimates (V) in
theorem GlobalTheory.ChernPull.chernTop_comp : ∀ {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (K : ReciprocityTheory.L2DbarEstimates.V n → Mat m ℂ) (φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n) (v : ReciprocityTheory.L2DbarEstimates.V n), AnalyticAt ℂ φ v → (∀ τ, MContDiffAt 2 (fun u => K u τ) (φ v)) → (∀ τ, IsUnit (K (φ v) τ).det) → chernTop R (fun w => K (φ w)) v = Complex.normSq (LinearMap.det (fderiv ℂ φ v : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V n)) * chernTop R K (φ v) := by
  intro n ι m R K φ v hφ h2 hu
  unfold chernTop
  have hc : ∀ x : ι × ℕ, chernPoly (fun u => K (φ u) x.1) v x.2 =
      GlobalTheory.ChernPull.substAlg (GlobalTheory.ChernPull.jac φ v) (chernPoly (fun u => K u x.1) (φ v) x.2) :=
    fun x => GlobalTheory.ChernPull.chernPoly_comp hφ (h2 x.1) (hu x.1) x.2
  simp only [hc]
  have ha := congrArg (fun F => F R) (MvPolynomial.comp_aeval (R := ℝ)
    (f := fun x : ι × ℕ => chernPoly (fun u => K u x.1) (φ v) x.2)
    ((GlobalTheory.ChernPull.substAlg (GlobalTheory.ChernPull.jac φ v)).restrictScalars ℝ))
  simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars'] at ha
  rw [← ha, GlobalTheory.ChernPull.substAlg, GlobalTheory.T.topDegreeFormCoeff_linearSubst_eq_absDet_sq_mul, Complex.mul_conj, GlobalTheory.ChernPull.jac_eq_toMatrix,
    LinearMap.det_toMatrix, Complex.re_ofReal_mul]
  ring
end
end
