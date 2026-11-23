module

public import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle077
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle266
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthHeckeQuotientLeCocycleSpanDeterminant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle304
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle316
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle004
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle338
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle332
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientIntegralUnit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

namespace GlobalTheory.CutDetOrd

open GlobalTheory.CutDet

theorem value_mem_ccOff :
    ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → ∀ f ∈ S.T', (∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → f x' = 0) → f S.π' ∈ ccOff i Xs π := by
  intro D i r ρ π Xs S _ hS _ f hf h0
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, -, ⟨b, -, hb⟩, -⟩, -, ⟨hπ, -⟩, -⟩ := hS
  obtain ⟨cf, hcf, -⟩ := hb f hf
  have huniq : ∀ c : Fin D.R.t.factorial → D.nd.T i,
      (0 : S.X' → D.nd.O i) = ∑ k, ((fun x' => (c k : D.nd.X i → D.nd.O i) (S.p x')) :
        S.X' → D.nd.O i) * b k → c = 0 := by
    intro c hc
    obtain ⟨c0, -, hc0⟩ := hb 0 (zero_mem _)
    rw [hc0 c hc, hc0 0 (by funext x'; simp)]
  have hz : ∀ k, ∀ x ∈ Xs, x ∉ D.nd.Z i → (cf k : D.nd.X i → D.nd.O i) x = 0 := by
    intro k x hx hZ
    refine cutVal_coord_eq_zero (D.nd.T i) (D.nd.T_sep i) S.p b huniq cf x (fun x' hp => ?_) k
    rw [← hcf]
    exact h0 x' (hp ▸ hx) (hp ▸ hZ)
  rw [hcf, Finset.sum_apply]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [Pi.mul_apply]
  refine Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨cf k, (cf k).2, hz k, ?_⟩)
  rw [hπ]

theorem exists_ne_zero : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → NoChiOff i r Xs → ∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → ∃ η : Fin D.R.nV → KK D.nd i, ∃ γ : GE D.nd, ((yg D.nd r S γ x').map (toK D.nd i)).mulVec η ≠ 0 := by
  intro D i r ρ π Xs S _ hG _ hN x' hx hZ
  have hrank : ((Eel D.nd S x').map (toK D.nd i)).rank = 1 := hG.2.2.2.2.2.2.2.2.2.2.1.1 x'
  by_contra hcon
  push Not at hcon
  have h0 : ∀ η : Fin D.R.nV → KK D.nd i, ((Eel D.nd S x').map (toK D.nd i)).mulVec η = 0 := by
    intro η
    apply hN _ hx hZ
    intro g
    have h := hcon η g
    have hy : yg D.nd r S g x' = rTwO D.nd i r (S.p x') g * Eel D.nd S x' - Eel D.nd S x' := by
      unfold yg
      rw [← Matrix.smul_mul]
      rfl
    rw [hy, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.sub_mulVec, sub_eq_zero,
      ← Matrix.mulVec_mulVec] at h
    exact h
  have hz : ((Eel D.nd S x').map (toK D.nd i)).mulVecLin = 0 := LinearMap.ext h0
  rw [← Matrix.finrank_range_mulVecLin, hz, LinearMap.range_zero, finrank_bot] at hrank
  exact zero_ne_one hrank

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → π ∈ D.nd.Z i → NoChiOff i r Xs → Module.length (D.nd.O i) (D.nd.O i ⧸ ccOff i Xs π) ≤ Module.length (D.nd.O i) ↥(cocRho i r S Xs) + ∑ c : Fin D.R.t, Module.length (D.nd.O i) ↥(cocChi i r S Xs c) := by
  intro D i r ρ π Xs S hr hS hπ _ hchi
  classical
  have h52 := value_mem_ccOff D i r ρ π Xs S hr hS hπ
  have h54 := exists_ne_zero D i r ρ π Xs S hr hS hπ hchi
  obtain ⟨-, -, hcomp, hsurj, -, -, -, -, -, -, -, h51, -⟩ := hS
  have hinj : Function.Injective (algebraMap (D.nd.O i) (KK D.nd i)) := IsFractionRing.injective _ _
  let A : Subalgebra (D.nd.O i) (S.X' → MatN D.nd i) := spanAlg S.T' (fun x' => rO D.nd i r (S.p x'))
  obtain ⟨g, γ, hγ⟩ := exists_gens A (yg D.nd r S)
  have hY : ∀ m, InY D.nd r S m → ∃ θ : Fin g → A, m = ∑ q, (θ q : S.X' → MatN D.nd i) * yg D.nd r S (γ q) := by
    rintro _ ⟨m, a, s, ha, rfl⟩
    exact hγ m a s ha
  obtain ⟨P, Q, hPQ, hQP, hconj⟩ := exists_conj S.e
  have hbl := fun a (ha : a ∈ A) => hconj _ _ _ (hcomp a ha)
  obtain ⟨⟨fρ, hfρ⟩, hχ⟩ := exists_homs hinj A S.π' P Q hPQ hQP S.ψρ S.ψχ hbl
  choose fχ hfχ using hχ
  let Rel : Submodule A (Fin g → A) :=
    { carrier := {θ | ∀ x', S.p x' ∈ Xs → (∑ q, (θ q : S.X' → MatN D.nd i) * yg D.nd r S (γ q)) x' = 0}
      add_mem' := fun {a b} ha hb x' hx => by
        have := congrArg₂ (· + ·) (ha x' hx) (hb x' hx)
        simpa [add_mul, Finset.sum_add_distrib] using this
      zero_mem' := fun x' _ => by simp
      smul_mem' := fun c θ hθ x' hx => by
        have := congrArg (fun z => (c : S.X' → MatN D.nd i) x' * z) (hθ x' hx)
        simpa [Finset.sum_apply, Finset.mul_sum, mul_assoc] using this }
  let d : Option (Fin D.R.t) → ℕ := blockDim D.R.r
  let ψ := blockHom fρ fχ
  have hψχ : ∀ c (a : A), ψ (some c) a = S.ψχ c a • (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) := by
    intro c a
    rw [← hfχ, ← Algebra.algebraMap_eq_smul_one]
    rfl
  have key := GlobalTheory.T.determinantLemma_discreteValuationRing_quotientLength_bound (D.nd.O i) A (Option (Fin D.R.t)) d ψ (by
    rintro (_ | c) B
    · obtain ⟨a, ha, rfl⟩ := hsurj B
      exact ⟨⟨a, ha⟩, hfρ _⟩
    · change Matrix (Fin 1) (Fin 1) (D.nd.O i) at B
      refine ⟨algebraMap _ _ (B 0 0), ((ψ (some c)).commutes _).trans ?_⟩
      change algebraMap _ (Matrix (Fin 1) (Fin 1) (D.nd.O i)) _ = B
      ext a b
      rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
      simp [Matrix.algebraMap_matrix_apply]) g Rel (ccOff i Xs π) (by
    intro n θ hθ m
    have hT := GlobalTheory.BlockDetPoly.main S.T' D.R.nV A h51 n g (fun k p q => θ k p q) (fun k p q => (θ k p q).2) m
    have h2 := h52 _ hT (by
      intro x' hx hz
      obtain ⟨η, s, hs⟩ := h54 x' hx hz
      rw [det_generic_eq_zero hinj (fun k p q => (θ k p q : S.X' → MatN D.nd i) x')
        (fun q => ((yg D.nd r S (γ q) x').map (toK D.nd i)).mulVec η) ?_ ?_, AddMonoidAlgebra.coeff_zero]
      · rfl
      · intro h0
        apply hs
        obtain ⟨t, ht⟩ := hγ 1 (fun _ => 1) (fun _ => s) (fun _ => A.one_mem)
        rw [Fin.sum_univ_one, one_mul] at ht

        rw [ht, Finset.sum_apply, ← RingHom.mapMatrix_apply, map_sum, Matrix.sum_mulVec]
        refine Finset.sum_eq_zero fun q _ => ?_
        rw [Pi.mul_apply, map_mul, ← Matrix.mulVec_mulVec, RingHom.mapMatrix_apply _ (yg D.nd r S (γ q) x'),
          show ((yg D.nd r S (γ q) x').map (toK D.nd i)).mulVec η = 0 from congrFun h0 q, Matrix.mulVec_zero]
      · intro k p
        have h3 := congrArg (fun z => ((toK D.nd i).mapMatrix z).mulVec η) (hθ k p x' hx)

        simp only [Finset.sum_apply, map_sum, Matrix.sum_mulVec, Pi.mul_apply, map_mul, map_zero,
        Matrix.zero_mulVec, ← Matrix.mulVec_mulVec] at h3
        exact h3)
    rw [det_generic_blocks hinj P Q hPQ hQP (fun k p q => (θ k p q : S.X' → MatN D.nd i) S.π')
      (fun k p q => S.ψρ (θ k p q)) (fun c k p q => S.ψχ c (θ k p q))
      (fun k p q => hbl _ (θ k p q).2)] at h2
    rw [Fintype.prod_option]
    convert h2 using 3
    congr 1
    · congr 1
      ext1 pa qb
      simp only [Matrix.of_apply, ← hfρ]
      rfl
    · refine Finset.prod_congr rfl fun c _ => ?_
      refine (Matrix.det_submatrix_equiv_self (Equiv.prodUnique (Fin g) (Fin 1)).symm _).symm.trans ?_
      congr 1
      ext1 p q
      simp [hψχ])
  refine key.trans ?_
  rw [Fintype.sum_option]
  refine add_le_add ?_ (Finset.sum_le_sum fun c _ => ?_)
  · exact length_sol_le A fρ S.ψρ hfρ (yg D.nd r S) γ (InY D.nd r S) (fun y => ∀ x', S.p x' ∈ Xs → y x' = 0)
      hY Rel (fun _ h => h) (fun _ _ => rfl)
  · exact length_sol_le A (ψ (some c)) _ (hψχ c) (yg D.nd r S) γ (InY D.nd r S)
      (fun y => ∀ x', S.p x' ∈ Xs → y x' = 0) hY Rel (fun _ h => h) (fun _ _ => rfl)

end GlobalTheory.CutDetOrd

end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.PolynomialInertiaAction

open GlobalTheory.Cut.PolyInertia

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → ∀ v ∈ D.nd.S i, PolyAt i r Xs π v → ∀ c : Fin D.R.t, resIne i (cocChi i r S Xs c) v = ⊥ := by
  intro D i r ρ π Xs S _ hG _ v hv hP c
  obtain ⟨P, hP0, hPu⟩ := hP
  obtain ⟨-, hdec, hψ, -, -, -, -, ⟨hT, -⟩, -, ⟨hπ, -⟩, -⟩ := hG
  set γ0 := D.nd.gam0 i v with hγ0
  let a : S.X' → MatN D.nd i := fun x' =>
    Polynomial.aeval (rO D.nd i r (S.p x') γ0) (P.map (evT D.nd i (S.p x')))
  have ha_eq : ∀ x', a x' = ∑ k : Fin (P.natDegree + 1),
      evT D.nd i (S.p x') (P.coeff k) • rO D.nd i r (S.p x') (γ0 ^ (k : ℕ)) := by
    intro x'
    simp only [a, aeval_map_eq_sum, map_pow]
  have ha : InR' D.nd r S a := by
    refine ⟨P.natDegree + 1, fun k x' => evT D.nd i (S.p x') (P.coeff k), fun k => γ0 ^ (k : ℕ),
      fun k => hT _ (P.coeff k).2, ?_⟩
    funext x'
    rw [ha_eq, Finset.sum_apply]
  have h1 : InR' D.nd r S 1 := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, ?_⟩
    funext x'
    simp
  have hchi : chiU D.nd i ((c : ℕ) + 1) γ0 = chiU D.nd i 1 γ0 :=
    (GlobalTheory.T.cyclotomicChar_unramified_away_from_ell D i v (D.nd.SQ_l i v (Or.inl hv)) γ0 (D.nd.locNd_chebotarevPlace_mem i v)).2 _
      (Nat.le_add_left _ _) c.2
  have hval : S.ψχ c a = (P.map (evT D.nd i π)).eval (D.nd.zeta i v) := by
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    let u := S.e.symm (0, Pi.single c 1)
    have hu : (S.e u).2 c = 1 := by simp [u]
    have e1 := congrArg (fun z => z.2 c) (hψ a ha u)
    simp only [hu, mul_one] at e1
    have e2 : ((a S.π').map (toK D.nd i)).mulVec u = ∑ k : Fin (P.natDegree + 1),
        toK D.nd i (evT D.nd i π (P.coeff k)) •
          (mapM (toK D.nd i) (rO D.nd i r π) (γ0 ^ (k : ℕ))).mulVec u := by
      rw [ha_eq, hπ]
      change ((toK D.nd i).mapMatrix _).mulVec u = _

      rw [map_sum, Matrix.sum_mulVec]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Matrix.smul_mulVec]
      congr 1
      ext p q
      simp [mapM]

    rw [e2, map_sum, Prod.snd_sum, Finset.sum_apply] at e1
    change toK D.nd i _ = toK D.nd i _

    rw [← e1, ← Polynomial.coe_aeval_eq_eval, aeval_map_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hdec]
    simp only [Prod.smul_snd, Pi.smul_apply, hu, mul_one, map_pow, hchi, smul_eq_mul, map_mul,
      Units.val_pow_eq_pow_val]
    rfl
  rw [resIne, cocChi, cocW, Submodule.map_span, Submodule.span_eq_bot]
  rintro _ ⟨_, ⟨φ, hφ, hφ0, rfl⟩, rfl⟩
  funext γ
  change φ (yg D.nd r S γ) = 0
  have hy : InY D.nd r S (yg D.nd r S γ) :=
    ⟨1, fun _ => 1, fun _ => γ, fun _ => h1, by simp⟩
  have hay : InY D.nd r S (a * yg D.nd r S γ) :=
    ⟨1, fun _ => a, fun _ => γ, fun _ => ha, by simp⟩
  have hz : φ (a * yg D.nd r S γ) = 0 := by
    refine hφ0 _ hay fun x' hx' => ?_
    have h := hP0 (S.p x') hx' γ γ.2
    have : yg D.nd r S γ x' = (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
        ((rO D.nd i r (S.p x') γ - ((chiU D.nd i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) • (1 : MatN D.nd i)) *
          Eel D.nd S x') := by
      rw [yg, sub_mul, smul_sub, smul_mul_assoc, one_mul, smul_smul, Units.inv_mul, one_smul]
    rw [Pi.mul_apply, this, mul_smul_comm, ← mul_assoc]
    simp only [a]
    rw [h, zero_mul, smul_zero]
  rw [hφ a ha _ hy, matKO_smul_one, hval] at hz
  exact hPu.smul_eq_zero.mp hz

end GlobalTheory.Cut.PolynomialInertiaAction
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

noncomputable section

namespace GlobalTheory.WachHyp

theorem jump_mem (S : LocalSituation.Sit) (T : LocLat S.G S.Qp S.LL S.O) (τ : S.K →ₐ[S.Qp] S.LL) (a : ℤ)
    (h : IsJumpV S.PD T.ρ τ a) : a ∈ LocalSituation.Jset S T := by
  intro e
  apply h
  unfold FildR DdRE
  rw [inf_right_comm, e, inf_right_comm]

theorem jumpsLet_const (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ)
    (hj : ∀ a ∈ LocalSituation.Jset S Y, -(M0 : ℤ) ≤ a ∧ a ≤ h0) :
    DeltaInvariantLattices.JumpsLet S.W Y (fun _ => M0) (fun _ => h0) := by
  intro τ i _ a ha
  exact Set.mem_Icc.2 (hj a (jump_mem S Y τ a ha))

theorem nBasis (S : LocalSituation.Sit) (E : S.Comparison₂) (he : DeltaInvariantLattices.WachEtaleComparison S.W E) (Y : LocLat S.G S.Qp S.LL S.O)
    (hY : IsCrys S.PD Y.ρ) : LocalSituation.NBasis S E Y (S.W.N Y) := by
  obtain ⟨⟨⟨r, b, hbN, huniq, hRW⟩, -⟩, -⟩ := he Y hY
  let v : Fin r → ↥(S.W.N Y) := fun j => ⟨b j, hbN j⟩
  have hli : LinearIndependent (LetA S.O S.n) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : ((∑ j, g j • v j : ↥(S.W.N Y)) : S.W.DD Y) = 0 := by rw [hg]; rfl
    have h0' : (0 : S.W.DD Y) = ∑ j, g j • b j := by
      rw [← h0]; simp [v]
    obtain ⟨a, -, ha⟩ := huniq 0 (S.W.N Y).zero_mem
    have e1 := ha g h0'
    have e2 := ha (fun _ => 0) (by simp)
    intro j
    rw [e1, ← e2]
  have hsp : ⊤ ≤ Submodule.span (LetA S.O S.n) (Set.range v) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨a, ha, -⟩ := huniq x hx
    have : (⟨x, hx⟩ : ↥(S.W.N Y)) = ∑ j, a j • v j := by
      apply Subtype.ext
      simp [v, ha]
    rw [this]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  refine ⟨Fin r, inferInstance, Module.Basis.mk hli hsp, ?_, ?_⟩
  · simp only [Module.Basis.mk_apply, v]
    rw [Fintype.linearIndependent_iff]
    intro c hc
    obtain ⟨a, -, ha⟩ := hRW 0
    have e1 := ha c hc.symm
    have e2 := ha (fun _ => 0) (by simp)
    intro j
    rw [e1, ← e2]
  · simp only [Module.Basis.mk_apply, v]
    rw [eq_top_iff]
    rintro y -
    obtain ⟨c, hc, -⟩ := hRW y
    rw [hc]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

theorem wClauses (S : LocalSituation.Sit) (E : S.Comparison₂) (h1 : DeltaInvariantLattices.WachLatticeFree S.W) (h5 : DeltaInvariantLattices.P5W S.W)
    (he : DeltaInvariantLattices.WachEtaleComparison S.W E) (Y : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (hY : IsCrys S.PD Y.ρ)
    (hj : ∀ a ∈ LocalSituation.Jset S Y, -(M0 : ℤ) ≤ a ∧ a ≤ h0) :
    LocalSituation.WClauses S E Y M0 h0 (S.W.N Y) := by
  have hf := h1 Y hY
  have hp := h5 Y (fun _ => M0) (fun _ => h0) hY (jumpsLet_const S Y M0 h0 hj)
  have hNl : ∀ i, S.W.Nl Y i ≤ S.W.N Y := fun i => by
    rw [hf.1]; exact le_iSup (fun j => S.W.Nl Y j) i
  refine ⟨nBasis S E he Y hY, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hf.1] at hx
    refine Submodule.iSup_induction (fun j => S.W.Nl Y j)
      (motive := fun x => S.W.Q ^ M0 • S.W.φD Y x ∈ S.W.N Y) hx ?_ ?_ ?_
    · intro j y hy
      exact hp.1 (j + 1) y (by simpa using hy)
    · simp
    · intro y z hy hz
      simp only [map_add (f := _), smul_add]
      exact add_mem hy hz
  · intro y hy
    rw [hf.1] at hy
    refine Submodule.iSup_induction (fun j => S.W.Nl Y j)
      (motive := fun y => S.W.Q ^ h0 • y ∈ LocalSituation.phiSpan S Y (S.W.N Y)) hy ?_ ?_ ?_
    · intro j y hy
      exact Submodule.span_mono (Set.image_mono (hNl (j - 1))) (hp.2.1 j y hy)
    · simp
    · intro y z hy hz
      simp only [smul_add]
      exact add_mem hy hz
  · intro g _ x hx
    exact S.W.N_Γ Y _ x hx
  · intro g _ x hx
    obtain ⟨y, hy, e⟩ := S.W.N_π Y (S.W.resΓ g) x hx
    rw [e]
    exact Submodule.smul_mem_smul (Ideal.subset_span rfl) hy
  · intro f x hx
    exact S.W.map_N f hY hY x hx

theorem hypW_crystalline : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), DeltaInvariantLattices.UsedLocalConclusion D HW F Cm → DeltaInvariantLattices.ConclusionE D HW F → CrysOnCond D HW F → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie := by
  intro D HW F Cm hU hE hC l _ K s LL h Y M0 h0 hY hj
  have hT := hU.1 l K s LL h
  exact LocalSituation.HypW_of_rec (hC l K s LL h Y hY) hj
    (wClauses _ _ hT.1 hT.2.2.2.2.1 (hE.1 l K s LL h) Y M0 h0 hY hj)

end GlobalTheory.WachHyp
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.Proof.LocDegPos

theorem locDeg_pos_and_sum_le : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ), l.Prime → (∀ v : HeightOneSpectrum (𝓞 E), 0 < Formalism.MainNotions.N.locDeg E v) ∧ ∀ s : Finset (HeightOneSpectrum (𝓞 E)), (∀ v ∈ s, v ∈ placesOver E l) → ∑ v ∈ s, Formalism.MainNotions.N.locDeg E v ≤ Module.finrank ℚ E := by
  intro E _ _ l hl
  refine ⟨fun v => ?_, fun s hs => ?_⟩
  · haveI := v.isPrime
    exact Nat.mul_pos (Ideal.ramificationIdx_pos (R := ℤ) v.asIdeal) (Ideal.inertiaDeg_pos v.asIdeal ℤ)
  · classical
    haveI : Fact l.Prime := ⟨hl⟩
    have hfin : Set.Finite {v : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ v.asIdeal} := by
      have hf : ((Ideal.span {(l : ℤ)}).primesOver (𝓞 E)).Finite :=
        IsDedekindDomain.primesOver_finite _ _
      refine Set.Finite.of_finite_image (f := fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal)
        (hf.subset ?_) (fun a _ b _ h => HeightOneSpectrum.ext h)
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨v.isPrime, ?_⟩
      rw [Ideal.liesOver_span_iff v.isPrime.ne_top (Nat.prime_iff_prime_int.1 hl)]
      simpa using hv
    letI : Fintype {v : HeightOneSpectrum (𝓞 E) // ((l : ℕ) : 𝓞 E) ∈ v.asIdeal} := hfin.fintype
    have hsum := GlobalTheory.Proof.LocalDegreeSum.sum_locDeg E l
    rw [← hsum, ← Finset.sum_subtype_of_mem (fun v => Formalism.MainNotions.N.locDeg E v) (p := fun v : HeightOneSpectrum (𝓞 E) => ((l : ℕ) : 𝓞 E) ∈ v.asIdeal) (fun v hv => hs v hv)]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end GlobalTheory.Proof.LocDegPos
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.ExtCrysCrit

theorem cocycle_of_ext {G LL V₀ V₁ : Type} [Group G] [TopologicalSpace G] [Field LL] [TopologicalSpace LL]
    [AddCommGroup V₀] [Module LL V₀] [TopologicalSpace V₀] [ContinuousAdd V₀] [ContinuousSMul LL V₀]
    [AddCommGroup V₁] [Module LL V₁] [TopologicalSpace V₁] [IsModuleTopology LL V₁]
    (ρ₀ : Representation LL G V₀) (ρ₁ : Representation LL G V₁) (ι : V₀ →ₗ[LL] V₁)
    (hι : Function.Injective ι) (hιρ : ∀ g y, ι (ρ₀ g y) = ρ₁ g (ι y)) (x : V₁)
    (hx : Continuous fun g => ρ₁ g x) (c : G → V₀) (hc : ∀ g, ι (c g) = ρ₁ g x - x) :
    Continuous c ∧ ∀ g h, c (g * h) = c g + ρ₀ g (c h) := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.2 hι)
  have hrc : ∀ g, c g = r (ρ₁ g x) + (- r x) := by
    intro g
    rw [← sub_eq_add_neg, ← map_sub, ← hc, ← LinearMap.comp_apply, hr, LinearMap.id_apply]
  refine ⟨?_, fun g h => hι ?_⟩
  · have : c = fun g => r (ρ₁ g x) + (- r x) := funext hrc
    rw [this]
    exact ((IsModuleTopology.continuous_of_linearMap r).comp hx).add continuous_const
  · rw [map_add (f := _), hιρ, hc, hc, hc, map_mul, Module.End.mul_apply, map_sub]
    abel

theorem finrank_ext {LL V₀ V₁ V₂ : Type} [Field LL] [AddCommGroup V₀] [Module LL V₀] [AddCommGroup V₁]
    [Module LL V₁] [FiniteDimensional LL V₁] [AddCommGroup V₂] [Module LL V₂]
    (ι : V₀ →ₗ[LL] V₁) (π : V₁ →ₗ[LL] V₂) (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hk : ∀ z, π z = 0 ↔ ∃ y, ι y = z) (h1 : Module.finrank LL V₂ = 1) :
    Module.finrank LL V₁ = Module.finrank LL V₀ + 1 := by
  have hk' : LinearMap.ker π = LinearMap.range ι := by
    ext z; rw [LinearMap.mem_ker, LinearMap.mem_range]; exact hk z
  have h := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.2 hπ, finrank_top, hk', LinearMap.finrank_range_of_inj hι, h1] at h
  omega

theorem not_mem_range {LL V₀ V₁ V₂ : Type} [Field LL] [AddCommGroup V₀] [Module LL V₀] [AddCommGroup V₁]
    [Module LL V₁] [AddCommGroup V₂] [Module LL V₂]
    (ι : V₀ →ₗ[LL] V₁) (π : V₁ →ₗ[LL] V₂) (hk : ∀ z, π z = 0 ↔ ∃ y, ι y = z) (x : V₁) (hx : π x ≠ 0) :
    x ∉ LinearMap.range ι := by
  rintro ⟨y, rfl⟩
  exact hx ((hk _).2 ⟨y, rfl⟩)

theorem blochKato_ext_all : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm15 D := by
  intro D l _ K LL
  intro T Tp To ι π hses htriv hdim hcrys x hxT hπx c hc
  have key := GlobalTheory.CrysExtCrit.coboundary_iff_isCrys l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ Tp.V Tp.ρ ι.f ι.equiv hses.1
    (finrank_ext ι.f π.f hses.1 hses.2.1 hses.2.2.2.1 hdim) hcrys x
    (not_mem_range ι.f π.f hses.2.2.2.1 x hπx) c hc
  obtain ⟨hcont, hcoc⟩ := cocycle_of_ext T.ρ Tp.ρ ι.f hses.1 ι.equiv x (Tp.cont x) c hc
  exact ⟨fun h => key.1 h.2, fun h => ⟨⟨hcont, hcoc⟩, key.2 h⟩⟩

end GlobalTheory.ExtCrysCrit
end

section

open GlobalTheory.UnitDiscAlg

theorem _root_.GlobalTheory.T.quotient_integral_unit_alt : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (N c b e₁ e₂ e₃ u a₂ a₃ : Matrix (Fin n) (Fin n) E) (ϖ : E), 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x) → IsUnit c → c * N = N * c → b * N = N * b → (∀ i j, ‖b i j‖ ≤ 1) → ‖b.det‖ = 1 → (e₁ * N = N * e₁ ∧ e₂ * N = N * e₂ ∧ e₃ * N = N * e₃ ∧ u * N = N * u ∧ a₂ * N = N * a₂ ∧ a₃ * N = N * a₃) → (∀ i j, ‖e₁ i j‖ ≤ 1 ∧ ‖e₂ i j‖ ≤ 1 ∧ ‖e₃ i j‖ ≤ 1 ∧ ‖u i j‖ ≤ 1 ∧ ‖a₂ i j‖ ≤ 1 ∧ ‖a₃ i j‖ ≤ 1) → ‖u.det‖ = 1 → e₁ * e₁ = e₁ → e₂ * e₂ = e₂ → e₃ * e₃ = e₃ → e₁ * e₂ = 0 → e₁ * e₃ = 0 → e₂ * e₃ = 0 → e₁ + e₂ + e₃ = 1 → c * e₁ = u * e₁ → c * e₂ = ϖ • (a₂ * e₂) → c⁻¹ * e₃ = ϖ • (a₃ * e₃) → IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) ∧ IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) ∧ IsUnit (ϖ • c ^ 2 + b ^ 2) ∧ IsUnit (ϖ • c ^ 3 + b ^ 3) ∧ (∀ i j, ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹) i j‖ ≤ 1) ∧ ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹).det‖ = 1 := by
  first | exact @GlobalTheory.UnitDiscAlg.QuotAlg.quotient_integral_unit | exact GlobalTheory.UnitDiscAlg.QuotAlg.quotient_integral_unit | (intros; apply GlobalTheory.UnitDiscAlg.QuotAlg.quotient_integral_unit <;> assumption)
end
