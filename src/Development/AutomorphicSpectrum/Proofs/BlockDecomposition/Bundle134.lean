module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle122
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle048
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockMatrixMultiplicative
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle101
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle123
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle124
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnimodularHermitianRepsCountSucc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle125

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.Axis

theorem rTensor_cocycle_eq_coboundary_of_class_eq_zero :
    ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (N : Type) [AddCommGroup N] [Module R N] (t : Z1 F ⊗[R] N), (H1.mk F).rTensor N t = 0 →
    ∃ g : ∀ T : C, F.obj T ⊗[R] N, ∀ (T T' : C) (φ : T ⟶ T'),
      (evZ F φ).rTensor N t = g T' - (mp F φ).toLinearMap.rTensor N (g T) := by
  intro R _ C _ F N _ _ t ht
  have hex : Function.Exact ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)) (H1.mk F) :=
    LinearMap.exact_map_mkQ_range _
  obtain ⟨u, rfl⟩ := (rTensor_exact N hex (H1.mk_surjective F) t).1 ht
  refine ⟨fun T => (LinearMap.proj T : C0 F →ₗ[R] F.obj T).rTensor N u, fun T T' φ => ?_⟩
  have key : evZ F φ ∘ₗ (d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F) =
      (LinearMap.proj T' : C0 F →ₗ[R] F.obj T') -
        (mp F φ).toLinearMap ∘ₗ (LinearMap.proj T : C0 F →ₗ[R] F.obj T) := by
    ext g
    rfl
  rw [← LinearMap.rTensor_comp_apply, key, LinearMap.rTensor_sub, LinearMap.sub_apply,
    LinearMap.rTensor_comp_apply]

end GlobalTheory.CompanionTheory.Axis
end

section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Axis.KFlat

section Pi

variable {R : Type} [CommRing R] {J : Type} [Finite J] {M : J → Type} [∀ i, AddCommGroup (M i)]
  [∀ i, Module R (M i)] {N : Type} [AddCommGroup N] [Module R N]

theorem piLeft_apply_eq [Fintype J] [DecidableEq J] (u : (∀ i, M i) ⊗[R] N) (i : J) :
    TensorProduct.piLeft R N M u i = (LinearMap.proj i : (∀ i, M i) →ₗ[R] M i).rTensor N u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]

theorem pi_rTensor_eq_zero (w : (∀ i, M i) ⊗[R] N)
    (h : ∀ i, (LinearMap.proj i : (∀ i, M i) →ₗ[R] M i).rTensor N w = 0) : w = 0 := by
  classical
  have := Fintype.ofFinite J
  apply (TensorProduct.piLeft R N M).injective
  funext i
  rw [piLeft_apply_eq, h, map_zero]
  rfl

theorem pi_rTensor_exists (g : ∀ i, M i ⊗[R] N) :
    ∃ u : (∀ i, M i) ⊗[R] N, ∀ i, (LinearMap.proj i : (∀ i, M i) →ₗ[R] M i).rTensor N u = g i := by
  classical
  have := Fintype.ofFinite J
  refine ⟨(TensorProduct.piLeft R N M).symm g, fun i ↦ ?_⟩
  rw [← piLeft_apply_eq, LinearEquiv.apply_symm_apply]

end Pi

theorem class_eq_zero_of_coboundary (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C] [Quiver.IsThin C]
    (F : C ⥤ CommAlgCat.{0} R) (N : Type) [AddCommGroup N] [Module R N] [Module.Flat R N] (t : Z1 F ⊗[R] N)
    (g : ∀ T : C, F.obj T ⊗[R] N)
    (h : ∀ (T T' : C) (φ : T ⟶ T'), (evZ F φ).rTensor N t = g T' - (mp F φ).toLinearMap.rTensor N (g T)) :
    (H1.mk F).rTensor N t = 0 := by
  classical
  haveI : ∀ T T' : C, Finite (T ⟶ T') := fun T T' ↦ by
    haveI : Subsingleton (T ⟶ T') := inferInstance
    exact Finite.of_subsingleton
  let κ : Z1 F →ₗ[R] ∀ x : (Σ T : C, Σ T' : C, (T ⟶ T')), F.obj x.2.1 :=
    LinearMap.pi fun x ↦ evZ F x.2.2
  have hκ : Function.Injective κ := fun a b hab ↦ Subtype.ext (by
    funext T T' φ
    exact congrFun hab ⟨T, T', φ⟩)
  let δ : C0 F →ₗ[R] Z1 F := (d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)
  obtain ⟨u, hu⟩ := pi_rTensor_exists (R := R) (M := fun T : C ↦ F.obj T) (N := N) g
  have hδ : ∀ {T T' : C} (φ : T ⟶ T'), evZ F φ ∘ₗ δ =
      (LinearMap.proj T' : C0 F →ₗ[R] F.obj T') -
        (mp F φ).toLinearMap ∘ₗ (LinearMap.proj T : C0 F →ₗ[R] F.obj T) := fun φ ↦ by
    refine LinearMap.ext fun c ↦ ?_
    rfl
  have key : t = δ.rTensor N u := by
    apply Module.Flat.rTensor_preserves_injective_linearMap κ hκ
    rw [← sub_eq_zero, ← map_sub]
    apply pi_rTensor_eq_zero
    rintro ⟨T, T', φ⟩
    rw [← LinearMap.rTensor_comp_apply]
    have e : (LinearMap.proj (⟨T, T', φ⟩ : Σ T : C, Σ T' : C, (T ⟶ T')) :
        (∀ x : (Σ T : C, Σ T' : C, (T ⟶ T')), F.obj x.2.1) →ₗ[R] F.obj T') ∘ₗ κ = evZ F φ := rfl
    rw [e, map_sub, h, ← LinearMap.rTensor_comp_apply, hδ, LinearMap.rTensor_sub, LinearMap.sub_apply,
      LinearMap.rTensor_comp_apply, hu, hu, sub_self]
  have hz : H1.mk F ∘ₗ δ = 0 := by
    refine LinearMap.ext fun c ↦ ?_
    exact (H1.mk_eq_zero (F := F) (f := δ c)).2 ⟨c, rfl⟩
  rw [key, ← LinearMap.rTensor_comp_apply, hz, LinearMap.rTensor_zero, LinearMap.zero_apply]

end GlobalTheory.CompanionTheory.Axis.KFlat
end
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.OrthCount

variable {E : Type} [CommRing E] {τ : E →+* E} {V : Type} [AddCommGroup V] [Module E V]

abbrev Tuples (B : HermSp E τ V) (n : ℕ) : Type :=
  {x : Fin n → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0}

theorem isUnit_norm (B : HermSp E τ V) (w : {w : V // B.h w w = 1}) : IsUnit (B.h w.1 w.1) := by
  rw [w.2]; exact isUnit_one

noncomputable def consEquiv (B : HermSp E τ V) (n : ℕ) :
    Tuples B (n + 1) ≃
      Σ w : {w : V // B.h w w = 1}, Tuples (B.perpForm (isUnit_norm B w)) n where
  toFun x := ⟨⟨x.1 0, by simpa using x.2 0 0⟩,
    ⟨fun j => ⟨x.1 j.succ, by
      show B.h (x.1 j.succ) (x.1 0) = 0
      simpa [Fin.succ_ne_zero] using x.2 j.succ 0⟩, fun i j => by
      simpa using x.2 i.succ j.succ⟩⟩
  invFun p := ⟨Fin.cons p.1.1 (fun j => (p.2.1 j : V)), by
    obtain ⟨⟨w, hw⟩, ⟨y, hy⟩⟩ := p
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hw
    · have h0 : B.h (y j : V) w = 0 := (y j).2
      simp [B.symm (y j : V) w, h0, (Fin.succ_ne_zero j).symm]
    · have h0 : B.h (y i : V) w = 0 := (y i).2
      simp [h0, Fin.succ_ne_zero i]
    · simpa using hy i j⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.cases rfl (fun j => rfl) i
  right_inv p := by
    obtain ⟨⟨w, hw⟩, ⟨y, hy⟩⟩ := p
    rfl

end GlobalTheory.CompanionTheory.UnrDens.OrthCount

namespace GlobalTheory.CompanionTheory.UnrDens


open OrthCount in
theorem card_orthonormal_tuples : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (n m : ℕ), n ≤ m → ∀ (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (Nat.card {x : Fin n → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0} : ℝ) = ∏ i : Fin n, ((q : ℝ) ^ (2 * (m - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ)))) := by
  intro E _ τ q ε hR n
  induction n with
  | zero =>
    intro m _ V _ _ B _
    have h1 : Nat.card {x : Fin 0 → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext (funext fun i => i.elim0)⟩,
        ⟨⟨fun i => i.elim0, fun i => i.elim0⟩⟩⟩
    simp [h1]
  | succ n ih =>
    intro m hnm V _ _ B hc
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hq : 1 < q := hR.one_lt
    have hq0 : q ≠ 0 := by omega
    haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hq0)
    haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hR.card]; exact pow_ne_zero _ hq0)
    haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hR.card]; nlinarith)
    have hsph := (GlobalTheory.T.hermitian_vector_values_card E τ q ε hR (m' + 1) V B hc).1 1 (map_one τ) one_ne_zero
    have hperp : ∀ w : {w : V // B.h w w = 1}, Nat.card (B.perp w.1) = q ^ (2 * m') := by
      intro w
      have h1 := Nat.card_congr (B.perpEquiv (isUnit_norm B w))
      rw [Nat.card_prod, hR.card, hc] at h1
      have h2 : q ^ (2 * (m' + 1)) = q ^ 2 * q ^ (2 * m') := by ring
      rw [h2] at h1
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (by omega) 2) h1
    have hfib : ∀ w : {w : V // B.h w w = 1},
        (Nat.card (Tuples (B.perpForm (isUnit_norm B w)) n) : ℝ) =
          ∏ i : Fin n, ((q : ℝ) ^ (2 * (m' - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m' - (i : ℕ)))) :=
      fun w => ih m' (by omega) (B.perp w.1) (B.perpForm (isUnit_norm B w)) (hperp w)
    haveI : Fintype {w : V // B.h w w = 1} := Fintype.ofFinite _
    have hcard : (Nat.card (Tuples B (n + 1)) : ℝ) =
        (Nat.card {w : V // B.h w w = 1} : ℝ) *
          ∏ i : Fin n, ((q : ℝ) ^ (2 * (m' - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m' - (i : ℕ)))) := by
      rw [Nat.card_congr (consEquiv B n), Nat.card_sigma]
      push_cast
      rw [Finset.sum_congr rfl (fun w _ => hfib w), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Nat.card_eq_fintype_card]
    change (Nat.card (Tuples B (n + 1)) : ℝ) = _
    rw [hcard, hsph, Fin.prod_univ_succ]
    simp [Nat.add_sub_add_right]

end GlobalTheory.CompanionTheory.UnrDens
end

section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem phi_eq_of_convex : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X), IsOpen Ω → Convex ℝ Ω → GaussTube G Ω →
    ∀ x ∈ Ω, ∀ x' ∈ Ω, ∀ t : ℝ × ℝ, phi G x t = phi G x' t := by
  intro X _ _ _ Ω G hΩ hconv hG x hx x' hx' t
  have hhor : ∀ a b c : ℝ, (∀ s ∈ Set.uIcc a b, (s, c) ∈ Ω) →
      GlobalTheory.CompanionTheory.TubeFourier.phi G (a, c) t = GlobalTheory.CompanionTheory.TubeFourier.phi G (b, c) t := by
    intro a b c h
    rcases le_total a b with hab | hba
    · exact GlobalTheory.T.tube_transform_horizontal_invariance X Ω G hG a b c hab
        (fun s hs => h s (Set.Icc_subset_uIcc hs)) t
    · exact (GlobalTheory.T.tube_transform_horizontal_invariance X Ω G hG b a c hba
        (fun s hs => h s (Set.Icc_subset_uIcc' hs)) t).symm
  have hver : ∀ a b c : ℝ, (∀ s ∈ Set.uIcc a b, (c, s) ∈ Ω) →
      GlobalTheory.CompanionTheory.TubeFourier.phi G (c, a) t = GlobalTheory.CompanionTheory.TubeFourier.phi G (c, b) t := by
    intro a b c h
    rcases le_total a b with hab | hba
    · exact GlobalTheory.T.tube_transform_vertical_invariance X Ω G hG a b c hab
        (fun s hs => h s (Set.Icc_subset_uIcc hs)) t
    · exact (GlobalTheory.T.tube_transform_vertical_invariance X Ω G hG b a c hba
        (fun s hs => h s (Set.Icc_subset_uIcc' hs)) t).symm
  have hf : IsLocallyConstant (fun p : Ω => GlobalTheory.CompanionTheory.TubeFourier.phi G (p : ℝ × ℝ) t) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨⟨p₁, p₂⟩, hp⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ (p₁, p₂) hp
    have hmem : {q : Ω | (q : ℝ × ℝ) ∈ Metric.ball (p₁, p₂) ε} ∈ 𝓝 (⟨(p₁, p₂), hp⟩ : Ω) :=
      continuousAt_subtype_val.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
    filter_upwards [hmem]
    rintro ⟨⟨q₁, q₂⟩, hq⟩ hqball
    have hd : dist q₁ p₁ < ε ∧ dist q₂ p₂ < ε := by
      have h' : dist (q₁, q₂) (p₁, p₂) < ε := hqball
      rwa [Prod.dist_eq, max_lt_iff] at h'
    obtain ⟨h₁, h₂⟩ := hd
    rw [Real.dist_eq] at h₁ h₂
    have hv : GlobalTheory.CompanionTheory.TubeFourier.phi G (q₁, p₂) t = GlobalTheory.CompanionTheory.TubeFourier.phi G (q₁, q₂) t := by
      refine hver p₂ q₂ q₁ (fun s hs => hball ?_)
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
      exact ⟨h₁, lt_of_le_of_lt (Set.abs_sub_left_of_mem_uIcc hs) h₂⟩
    have hh : GlobalTheory.CompanionTheory.TubeFourier.phi G (p₁, p₂) t = GlobalTheory.CompanionTheory.TubeFourier.phi G (q₁, p₂) t := by
      refine hhor p₁ q₁ p₂ (fun s hs => hball ?_)
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_self, Real.dist_eq]
      exact ⟨lt_of_le_of_lt (Set.abs_sub_left_of_mem_uIcc hs) h₁, hε⟩
    show GlobalTheory.CompanionTheory.TubeFourier.phi G (q₁, q₂) t = GlobalTheory.CompanionTheory.TubeFourier.phi G (p₁, p₂) t
    rw [← hv, ← hh]
  haveI : PreconnectedSpace Ω := Subtype.preconnectedSpace hconv.isPreconnected
  exact hf.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ (⟨x, hx⟩ : Ω))
    (Set.mem_univ (⟨x', hx'⟩ : Ω))

end GlobalTheory.CompanionTheory.TubeFourier
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix


theorem _root_.GlobalTheory.T.delta_block_matrix_multiplicative : ∀ (F E : Type) [Field F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (m : ℕ) (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E), delta (blk σ c u d) = delta c * Ideal.absNorm (tor c u) * idx E (lastFib (blk σ c u d)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.IndexFormula.delta_blk | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.IndexFormula.delta_blk | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.IndexFormula.delta_blk <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.MeanV

theorem support_finite (hC : CountBd) (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (T : Finset (HeightOneSpectrum (𝓞 F))) (K : Set (Ainf F))
    (hK : IsCompact K) (Kv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hKv : ∀ v ∈ T, IsCompact (Kv v))
    (δ : ℝ) (hδ : 0 < δ) :
    {x : F | x ≠ 0 ∧ x ∈ IntOut T ∧ θ δ * algebraMap F (Ainf F) x ∈ K ∧
      ∀ v ∈ T, algebraMap F (Fv F v) x ∈ Kv v}.Finite := by
  obtain ⟨N, hN, hNx⟩ := GlobalTheory.T.exists_integral_multiple_bounded_places F T Kv hKv
  obtain ⟨C0, h⟩ := hC F hF θ hθ K hK N hN
  refine ((h δ hδ ⊤ top_ne_bot).1).subset ?_
  rintro x ⟨h0, h1, h2, h3⟩
  obtain ⟨y, hy⟩ := hNx x h1 h3
  exact ⟨h0, ⟨y, Submodule.mem_top, hy⟩, h2⟩

theorem tsum_ne_zero_eq_sum {F : Type} [Field F] (h : F → ℝ) (B : Finset F) (hB : ∀ x ∈ B, x ≠ 0)
    (hh : ∀ x, x ≠ 0 → x ∉ B → h x = 0) :
    ∑' β : {β : F // β ≠ 0}, h β.1 = ∑ x ∈ B, h x := by
  have h1 : ∑' β : {β : F // β ≠ 0}, h β.1 = ∑ β ∈ B.subtype (fun x => x ≠ 0), h β.1 := by
    refine tsum_eq_sum ?_
    intro b hb
    exact hh b.1 b.2 (by simpa [Finset.mem_subtype] using hb)
  rw [h1]
  refine Finset.sum_bij (fun b _ => b.1) ?_ ?_ ?_ ?_
  · intro a ha; simpa [Finset.mem_subtype] using ha
  · intro a _ b _ hab; exact Subtype.ext hab
  · intro b hb; exact ⟨⟨b, hB b hb⟩, by simpa [Finset.mem_subtype] using hb, rfl⟩
  · intro a _; rfl

theorem truncTerm_finite (hC : CountBd) (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (hGc : HasCompactSupport G)
    (hψ : ∀ v ∈ T, HasCompactSupport (ψ v)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : Finset F, (∀ x ∈ B, x ≠ 0) ∧ ∀ x, x ≠ 0 → x ∉ B → (IntOut T).indicator
      (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, ψ v (algebraMap F (Fv F v) x)) x = 0 := by
  have hfin := support_finite hC F hF θ hθ T (tsupport G) hGc (fun v => tsupport (ψ v)) hψ δ hδ
  refine ⟨hfin.toFinset, fun x hx => ((hfin.mem_toFinset).1 hx).1, ?_⟩
  intro x hx0 hxB
  by_cases hxT : x ∈ IntOut T
  · rw [Set.indicator_of_mem hxT]
    by_cases h1 : θ δ * algebraMap F (Ainf F) x ∈ tsupport G
    · have : ∃ v ∈ T, algebraMap F (Fv F v) x ∉ tsupport (ψ v) := by
        by_contra hcon
        push_neg at hcon
        exact hxB ((hfin.mem_toFinset).2 ⟨hx0, hxT, h1, hcon⟩)
      obtain ⟨v, hv, hvx⟩ := this
      have h0 : ψ v (algebraMap F (Fv F v) x) = 0 := image_eq_zero_of_notMem_tsupport hvx
      rw [Finset.prod_eq_zero hv h0, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]
  · exact Set.indicator_of_notMem hxT _

theorem truncTerm_summable (hC : CountBd) (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (hGc : HasCompactSupport G)
    (hψ : ∀ v ∈ T, HasCompactSupport (ψ v)) (δ : ℝ) (hδ : 0 < δ) :
    Summable fun β : {β : F // β ≠ 0} => (IntOut T).indicator
      (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, ψ v (algebraMap F (Fv F v) x)) β.1 := by
  obtain ⟨B, hB, hh⟩ := truncTerm_finite hC F hF θ hθ T G ψ hGc hψ δ hδ
  refine summable_of_ne_finset_zero (s := B.subtype (fun x => x ≠ 0)) ?_
  intro b hb
  exact hh b.1 b.2 (by simpa [Finset.mem_subtype] using hb)

end GlobalTheory.CompanionTheory.Mass.MeanV

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi

namespace GlobalTheory.CompanionTheory.MirFourier

theorem exists_finset_eq_sum_polyBall_translates :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] (φ : (Fin n → k) → E) (s S : kˣ), (∀ v a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall (k := k) n s → φ (v + a) = φ v) → (∀ v : Fin n → k, φ v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) n S) → ∃ R : Finset (Fin n → k), ∀ v : Fin n → k, φ v = ∑ x ∈ R, @ite _ (Multiplicative.ofAdd (v - x) ∈ polyBall (k := k) n s) (Classical.propDecidable _) (φ x) 0 := by
  intro k _ _ _ _ n E _ _ φ s S hinv hsupp
  classical
  set L := polyBall (k := k) n s with hL
  let q : Multiplicative (Fin n → k) → Multiplicative (Fin n → k) ⧸ L := QuotientGroup.mk
  have hopen : IsOpen (L : Set (Multiplicative (Fin n → k))) := isOpen_polyBall n s
  have hcov : ∃ T : Finset (Multiplicative (Fin n → k)),
      ((polyBall (k := k) n S : Subgroup _) : Set (Multiplicative (Fin n → k))) ⊆
        ⋃ x ∈ T, (fun y => x * y) '' (L : Set (Multiplicative (Fin n → k))) := by
    refine (isCompact_polyBall n S).elim_finite_subcover
      (fun x : Multiplicative (Fin n → k) => (fun y => x * y) '' (L : Set (Multiplicative (Fin n → k))))
      (fun x => (Homeomorph.mulLeft x).isOpenMap _ hopen) ?_ |>.imp fun T hT => ?_
    · intro x _
      exact Set.mem_iUnion.2 ⟨x, 1, L.one_mem, by simp⟩
    · simpa using hT
  obtain ⟨T, hT⟩ := hcov
  let f : Multiplicative (Fin n → k) ⧸ L → (Fin n → k) := fun c => (Quotient.out c).toAdd
  have hf : Function.Injective f := fun a b hab =>
    Quotient.out_injective (Multiplicative.toAdd.injective hab)
  have hmem : ∀ (v : Fin n → k) (c : Multiplicative (Fin n → k) ⧸ L),
      Multiplicative.ofAdd (v - f c) ∈ L ↔ q (Multiplicative.ofAdd v) = c := by
    intro v c
    have hc : q (Quotient.out c) = c := QuotientGroup.out_eq' c
    have hinvEq : Multiplicative.ofAdd (v - f c) =
        ((Multiplicative.ofAdd v)⁻¹ * Quotient.out c)⁻¹ := by
      apply Multiplicative.toAdd.injective
      simp [f, sub_eq_add_neg, add_comm]
    rw [hinvEq, L.inv_mem_iff, ← QuotientGroup.eq]
    exact (by rw [hc] : q (Multiplicative.ofAdd v) = q (Quotient.out c) ↔ _)
  have hval : ∀ v : Fin n → k, φ (f (q (Multiplicative.ofAdd v))) = φ v := by
    intro v
    have h := hinv (f (q (Multiplicative.ofAdd v))) (v - f (q (Multiplicative.ofAdd v)))
      ((hmem v _).2 rfl)
    rw [add_sub_cancel] at h
    exact h.symm
  refine ⟨(T.image q).image f, fun v => ?_⟩
  rw [Finset.sum_image (fun a _ b _ h => hf h)]
  by_cases hv : q (Multiplicative.ofAdd v) ∈ T.image q
  · rw [Finset.sum_eq_single_of_mem _ hv
      (fun b _ hb => if_neg (fun h => hb ((hmem v b).1 h).symm)),
      if_pos ((hmem v _).2 rfl), hval]
  · have h0 : φ v = 0 := by
      by_contra hne
      obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hT (hsupp v hne))
      refine hv (Finset.mem_image.2 ⟨x, hx, ?_⟩)
      have hxv : x⁻¹ * Multiplicative.ofAdd v ∈ L := by
        rw [← hxy]
        simpa using hy
      exact QuotientGroup.eq.2 hxv
    rw [h0]
    refine (Finset.sum_eq_zero fun b hb => if_neg fun h => hv ?_).symm
    rw [(hmem v b).1 h]
    exact hb

end GlobalTheory.CompanionTheory.MirFourier
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

theorem _root_.GlobalTheory.T.unimodular_hermitian_reps_count_succ : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R), IsUnimod σ S → IsUnimod σ T → ∀ k : ℕ, 1 ≤ k → solCount σ ϖ S T (k + 1) = solCount σ ϖ S T k * q ^ (2 * m * n - n ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.solCount_succ | exact GlobalTheory.CompanionTheory.UnrDens.solCount_succ | (intros; apply GlobalTheory.CompanionTheory.UnrDens.solCount_succ <;> assumption)
end
