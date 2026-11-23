module

public import Formalism.LocalToGlobal.Divisibility.Inputs
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

noncomputable section

namespace GlobalTheory.DefRowsCB

theorem exists_cbData : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (m : ℕ) (c : Fin (m + 1) → ℕ) (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ) (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K) (t : Fin m → InfinitePlace K → ℝ), (∀ i v, IsUnit (Xc i v).det) → (∀ j v x, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v ((Kj j).mulVec x) ^ 2 ≤ Real.exp (t j v) * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc) v x ^ 2) → ∃ cb : CBData Xc Kj, ∀ j v, Real.log (cb.sq j v) ≤ t j v := by
  intro K _ _ _ _ m c Xc Kj t hX h
  refine ⟨{
    AA := fun _ => Unit
    Cl := fun _ _ => Unit
    W := fun i _ => EuclideanSpace ℂ (Fin (c i))
    γ := fun _ _ => 1
    Φ := fun i v x _ => WithLp.toLp 2 ((Xc i v)⁻¹.mulVec x)
    ε := fun _ _ _ _ => 1
    T := fun j v _ _ => LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
      ((Xc j.succ v)⁻¹ * (Kj j).map v.embedding * Xc j.castSucc v))
    hcl := fun _ => 1
    tmax := fun j v => Real.exp (t j v)
    hyp := ⟨hX, fun _ _ => ⟨one_pos, le_rfl⟩, ?_, ?_, fun _ _ _ _ => norm_one, ?_,
      fun _ _ => (Real.exp_pos _).le, fun _ _ => by simp⟩ }, ?_⟩
  · intro i v x
    rw [Formalism.DivisionValues.fnorm, Formalism.HN.PlaceOperatorNorms.cnorm_eq]
    simp
  · intro j v x
    funext q
    simp only [Formalism.DimensionVariation.liftOp, Fintype.sum_sigma, Finset.univ_unique, Finset.sum_singleton, Complex.ofReal_one,
      mul_one, one_smul, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hX _ v), Matrix.mul_one]
  · intro j v _ _
    have key := Formalism.BasicNotions.opNormAt_sq_le (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) (hX _) v (IsTotallyComplex.isComplex v)
      (Matrix.mulVecLin (Kj j)) (Real.exp (t j v)) (Real.exp_pos _).le (fun x => by
        rw [← Formalism.BasicNotions.normAt_sq_eq_majAt, ← Formalism.BasicNotions.normAt_sq_eq_majAt]
        exact h j v x)
    have hm : LinearMap.toMatrix (Pi.basisFun K (Fin (c j.castSucc))) (Pi.basisFun K (Fin (c j.succ)))
        (Matrix.mulVecLin (Kj j)) = Kj j := by
      ext a b
      simp [LinearMap.toMatrix_apply]
    have e : Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
        (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) =
        ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin ((Xc j.succ v)⁻¹ *
          (LinearMap.toMatrix (Pi.basisFun K (Fin (c j.castSucc))) (Pi.basisFun K (Fin (c j.succ)))
            (Matrix.mulVecLin (Kj j))).map v.embedding * Xc j.castSucc v))‖ := rfl
    rw [e, hm] at key
    exact key
  · intro j v
    show Real.log (Formalism.DimensionVariation.cbSq (Fintype.card Unit) (Fintype.card Unit) 1 1 (Real.exp (t j v))) ≤ t j v
    simp [Formalism.DimensionVariation.cbSq]

end GlobalTheory.DefRowsCB
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder Pointwise

namespace GlobalTheory.ExponentsFinite

theorem val_le_one {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {p s : ℕ}
    (hp : ((p : ℕ) : 𝓞 K) ∈ P.asIdeal) (hs : Nat.Coprime s p) {x : K} (hx : IsIntegral ℤ ((s : K) * x)) :
    P.valuation K x ≤ 1 := by
  have hsP : ((s : ℕ) : 𝓞 K) ∉ P.asIdeal := by
    intro h
    obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hs).map (Int.castRingHom (𝓞 K))
    simp only [eq_intCast, Int.cast_natCast] at hab
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h) (P.asIdeal.mul_mem_left _ hp)))
  have h1 := (P.valuation_eq_one_iff_notMem (K := K)).2 hsP
  have h2 := P.valuation_le_one (K := K) (⟨_, hx⟩ : 𝓞 K)
  rw [map_natCast] at h1
  change P.valuation K ((s : K) * x) ≤ 1 at h2
  rwa [map_mul, h1, one_mul] at h2

theorem val_det_le_one {K ι Γ : Type} [Field K] [Fintype ι] [DecidableEq ι] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (f : (ι → K) →ₗ[K] (ι → K)) (hf : ∀ i j, v (f (Pi.single j 1) i) ≤ 1) :
    v (LinearMap.det f) ≤ 1 := by
  rw [← LinearMap.det_toMatrix', Matrix.det_apply']
  have : ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, LinearMap.toMatrix' f (σ i) i ∈ v.integer := by
    refine Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _) (Subring.prod_mem _ fun i _ => ?_)
    rw [LinearMap.toMatrix'_apply]
    exact hf _ _
  exact this

theorem val_det_eq_one {K ι Γ : Type} [Field K] [Fintype ι] [DecidableEq ι] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (f : (ι → K) ≃ₗ[K] (ι → K)) (hf : ∀ i j, v (f (Pi.single j 1) i) ≤ 1)
    (hf' : ∀ i j, v (f.symm (Pi.single j 1) i) ≤ 1) :
    v (LinearMap.det (f : (ι → K) →ₗ[K] (ι → K))) = 1 := by
  have h1 := val_det_le_one v (f : (ι → K) →ₗ[K] (ι → K)) hf
  have h2 := val_det_le_one v (f.symm : (ι → K) →ₗ[K] (ι → K)) hf'
  have h3 := congrArg v (LinearEquiv.det_mul_det_symm f)
  rw [map_mul, map_one] at h3
  refine le_antisymm h1 ?_
  calc 1 = _ := h3.symm
    _ ≤ v (LinearMap.det (f : (ι → K) →ₗ[K] (ι → K))) * 1 := by gcongr
    _ = _ := mul_one _

theorem exists_den {K ι : Type} [Field K] [NumberField K] [Finite ι] (c : ι → K) :
    ∃ n : ℕ, 0 < n ∧ ∀ i, IsIntegral ℤ ((n : K) * c i) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image c)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun i => ?_⟩
  have h := hy (c i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [zsmul_eq_mul] at h
  rcases Int.natAbs_eq y with h1 | h1
  · rw [h1, Int.cast_natCast] at h; exact h
  · rw [h1, Int.cast_neg, Int.cast_natCast, neg_mul] at h; simpa using h.neg

theorem exists_den_fg {K E ι κ : Type} [Field K] [NumberField K] [AddCommGroup E] [Finite ι] [Fintype κ]
    (A : Submodule ℤ E) (hA : A.FG) (g : (κ → E) →+ (ι → K)) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : κ → E, (∀ a, x a ∈ A) → ∀ w, IsIntegral ℤ ((n : K) * g x w) := by
  classical
  obtain ⟨S, hS⟩ := hA
  obtain ⟨n, hn, h⟩ := exists_den (fun t : S × κ × ι => g (Pi.single t.2.1 (t.1 : E)) t.2.2)
  refine ⟨n, hn, fun x hx w => ?_⟩
  have key : ∀ a, ∀ y ∈ Submodule.span ℤ (S : Set E), IsIntegral ℤ ((n : K) * g (Pi.single a y) w) := by
    intro a y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h (⟨y, hy⟩, a, w)
    | zero => simpa using isIntegral_zero
    | add y z _ _ hy hz => rw [Pi.single_add, map_add (f := _), Pi.add_apply, mul_add]; exact hy.add hz
    | smul c y _ hy =>
      rw [Pi.single_smul, map_zsmul, Pi.smul_apply, mul_smul_comm]; exact hy.zsmul c

  rw [← Finset.univ_sum_single x, map_sum, Finset.sum_apply, Finset.mul_sum]
  exact IsIntegral.sum _ fun a _ => key a _ (hS ▸ hx a)

theorem one_mem (D : D7) : (1 : D.host.E) ∈ D.host.AA0 := by
  have hb : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h => by
      have h3 : D.host.𝔟 ⊔ D.host.conj • D.host.𝔟 = ⊤ := D.host.𝔟_spec.2
      simp [h] at h3
  refine (FractionalIdeal.mem_inv_iff hb).2 fun y hy => ?_
  rw [one_mul]; exact FractionalIdeal.coeIdeal_le_one hy

theorem yFinite : ∀ (D : D7) (γ₀ : IsoK D) (k : KapChoice γ₀), k.YFinite := by
  classical
  intro D γ₀ k
  have hfg : ((D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).restrictScalars ℤ).FG :=
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl D.host.AA0).restrictScalars
  obtain ⟨n, hn, hnx⟩ := exists_den_fg _ hfg γ₀.g.toLinearMap.toAddMonoidHom
  obtain ⟨m, hm, hmx⟩ := exists_den
    (fun t : (Fin 4 × D.what₂.Tau) × Fin 4 => γ₀.g.symm (Pi.single t.1 1) t.2)
  refine (Set.finite_le_nat (n * m)).subset ?_
  rintro p ⟨hp, hsp, hy⟩
  by_contra hlt
  have hlt' : n * m < p := not_le.1 hlt
  have hcop : Nat.Coprime (n * m) p := (Nat.coprime_of_lt_prime (by positivity) hlt' hp).symm
  have hcn : Nat.Coprime n p := Nat.Coprime.coprime_mul_right hcop
  have hcm : Nat.Coprime m p := Nat.Coprime.coprime_mul_left hcop
  obtain ⟨h1, h2⟩ := k.gaP_at p hp hsp
  have hP := k.pp_over p hp hsp
  apply hy
  unfold KapChoice.yP ordK IsoK.detRel
  rw [val_det_eq_one]
  · simp
  · intro i j
    obtain ⟨s, hs, hsx⟩ := h1 (m • γ₀.g.symm (Pi.single j 1)) (fun a => by
      have := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem ⟨_, hmx (j, a)⟩ (one_mem D)
      change ((m : D.host.E) * γ₀.g.symm (Pi.single j 1) a) * 1 ∈ D.host.AA0 at this
      simpa using this)
    obtain ⟨r, hr⟩ := hsx i
    refine val_le_one _ hP (Nat.Coprime.mul_left hs hcm) ?_
    have hi : IsIntegral ℤ (algebraMap (𝓞 D.host.K) D.host.K r) := r.2
    rw [hr, map_nsmul, Pi.smul_apply, nsmul_eq_mul, ← mul_assoc] at hi
    simpa using hi
  · intro i j
    obtain ⟨s, hs, hsx⟩ := h2 (Pi.single j 1) (fun w => by
      by_cases hw : w = j
      · subst hw; simp
      · simp [hw])
    have hi := hnx (s • (k.gaP p).g.symm (Pi.single j 1)) (fun a => by
      have := hsx a
      simpa using this) i
    refine val_le_one _ hP (Nat.Coprime.mul_left hcn hs) ?_
    rw [map_nsmul, Pi.smul_apply, nsmul_eq_mul, ← mul_assoc] at hi
    simpa using hi

end GlobalTheory.ExponentsFinite
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.NatAtStd

theorem isSD_pi (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ) :
    IsSDLat E N (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) := by
  have hr : ∀ x : E, x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x := fun x =>
    ⟨by rintro ⟨a, rfl⟩; exact a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  have hm : ∀ x : Fin N → E, x ∈ (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) ↔
      ∀ k, IsIntegral ℤ (x k) := fun x => by
    simp only [Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
    exact forall_congr' fun k => hr (x k)
  have hs : ∀ k : Fin N, (Pi.single k 1 : Fin N → E) ∈
      (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) := fun k => by
    rw [hm]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  refine ⟨Submodule.fg_pi fun _ => ?_, ?_, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin N)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    simpa using hs k
  · rw [hr]
    rw [hm] at hx hy
    exact IsIntegral.sum _ fun i _ => ((hx i).map (starRingEnd E).toIntAlgHom).mul (hy i)
  · rw [hm]
    intro k
    have := h _ (hs k)
    rw [hr] at this
    simpa [stdH, Pi.single_apply, apply_ite] using this

theorem detId_std (D : D7) (N : ℕ) : TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N) = 1 := by
  classical
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨A, hA, rfl⟩
    have h : ∀ i j, ∃ b : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E b = A i j := fun i j => by
      have h1 : (Pi.single j 1 : Fin N → D.host.E) ∈ StandardLatticesGL3.stdL D N := fun k _ => by
        by_cases e : k = j
        · subst e
          rw [Pi.single_eq_same]
          exact Submodule.one_le.1 le_rfl
        · rw [Pi.single_eq_of_ne e]
          exact Submodule.zero_mem _
      have h2 := Submodule.mem_one.1 (hA _ h1 i trivial)
      simpa using h2
    choose b hb using h
    have e : A = (algebraMap (𝓞 D.host.E) D.host.E).mapMatrix (Matrix.of b) :=
      Matrix.ext fun i j => (hb i j).symm
    rw [e, ← RingHom.map_det]
    exact Submodule.mem_one.2 ⟨_, rfl⟩
  · exact Submodule.one_le.2 (Submodule.subset_span ⟨1, fun v hv => by simpa using hv, Matrix.det_one.symm⟩)

theorem chi_one (D : D7) (χ : TaylorLogMetric.IdE D → ℂ) (h : TaylorLogMetric.IsChi D χ) : χ 1 = 1 := by
  letI := D.host.cmStar
  have h1 := h.2 1
  rw [Submodule.one_eq_span]
  simpa using h1

theorem chiFac_std (D : D7) (χ : TaylorLogMetric.IdE D → ℂ) (h : TaylorLogMetric.IsChi D χ) (a b : ℕ) :
    Base.chiFac χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = 1 := by
  simp [Base.chiFac, detId_std, chi_one D χ h]

variable (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ}

theorem Iop_self (A : AddSubgroup (TaylorLogMetric.VC D N N')) :
    ∃ x ∈ A, ∀ G : TaylorLogMetric.VC D N N' → ℂ, TaylorLogMetric.Iop D T A A G = fun z => TaylorLogMetric.al D T x * TaylorLogMetric.U D T x G z := by
  have htop : A.addSubgroupOf A = ⊤ := AddSubgroup.addSubgroupOf_self A
  haveI hsub : Subsingleton (A ⧸ A.addSubgroupOf A) := by
    rw [htop]; exact QuotientAddGroup.subsingleton_quotient_top
  let q0 : A ⧸ A.addSubgroupOf A := QuotientAddGroup.mk 0
  refine ⟨((Quotient.out q0 : A) : TaylorLogMetric.VC D N N'), Subtype.property _, fun G => ?_⟩
  funext z
  have hi : (A.addSubgroupOf A).index = 1 := by rw [htop]; exact AddSubgroup.index_top
  unfold TaylorLogMetric.Iop
  rw [finsum_eq_single _ q0 (fun q hq => absurd (Subsingleton.elim q q0) hq), hi]
  simp

theorem Hf_neg_right (z x : TaylorLogMetric.VC D N N') : TaylorLogMetric.Hf D T z (-x) = -TaylorLogMetric.Hf D T z x := by
  simp [TaylorLogMetric.Hf, neg_div]

theorem Hf_neg_left (z x : TaylorLogMetric.VC D N N') : TaylorLogMetric.Hf D T (-z) x = -TaylorLogMetric.Hf D T z x := by
  simp [TaylorLogMetric.Hf, neg_div]

theorem Hf_add_left (z w x : TaylorLogMetric.VC D N N') : TaylorLogMetric.Hf D T (z + w) x = TaylorLogMetric.Hf D T z x + TaylorLogMetric.Hf D T w x := by
  simp [TaylorLogMetric.Hf, add_mul, Finset.sum_add_distrib, add_div]

theorem al_neg_mul (x : TaylorLogMetric.VC D N N') : TaylorLogMetric.al D T (-x) * TaylorLogMetric.al D T x = 1 := by
  unfold TaylorLogMetric.al
  rw [Hf_neg_left, Hf_neg_right, neg_neg, ← mul_zpow]
  simp

theorem inv_op (x : TaylorLogMetric.VC D N N') (G : TaylorLogMetric.VC D N N' → ℂ) (z : TaylorLogMetric.VC D N N') :
    TaylorLogMetric.al D T (-x) * TaylorLogMetric.U D T (-x) (fun w => TaylorLogMetric.al D T x * TaylorLogMetric.U D T x G w) z = G z := by
  have h := al_neg_mul D T x
  unfold TaylorLogMetric.U
  simp only [Hf_add_left, Hf_neg_left, Hf_neg_right, neg_add_cancel_right]
  have he : Complex.exp (-(Real.pi : ℂ) * (TaylorLogMetric.Hf D T z x + -TaylorLogMetric.Hf D T x x) - (Real.pi : ℂ) * TaylorLogMetric.Hf D T x x / 2) *
      Complex.exp (-(Real.pi : ℂ) * -TaylorLogMetric.Hf D T z x - (Real.pi : ℂ) * - -TaylorLogMetric.Hf D T x x / 2) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  linear_combination (G z) * he * (TaylorLogMetric.al D T (-x) * TaylorLogMetric.al D T x) + G z * h

theorem eNat_std : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → B.VecP χ → ∀ a b : ℕ, Even a → Even b → TaylorLogMetric.admitted D a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) ∧ B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = B.thZero a b := by
  intro D cc dl B χ hχ hV a b ha hb
  have hA : TaylorLogMetric.admitted D a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) := by
    letI := D.host.cmStar
    exact ⟨ha, hb, isSD_pi _ a, isSD_pi _ b⟩
  refine ⟨hA, ?_⟩
  obtain ⟨x, hx, hI⟩ := Iop_self D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b))
  have hTh : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) ∈ TaylorLogMetric.Th D B.tor (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) :=
    (hV a b _ _ hA).1
  have hfix := hTh.2 (-x) (neg_mem hx)
  have he : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = fun z => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x
      (fun w => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x (B.thZero a b) w) z := by
    funext z
    unfold Base.eNat Base.thMoved Base.thHalf
    rw [chiFac_std D χ hχ, one_mul, hI, hI]
  have h1 : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) =
      fun w => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x (B.thZero a b) w := by
    funext z
    rw [← hfix z]
    conv_lhs => rw [he]
    exact inv_op D B.tor x _ z
  funext z
  rw [← hfix z]
  conv_lhs => rw [h1]
  exact inv_op D B.tor x _ z

end GlobalTheory.NatAtStd
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchKernel

theorem mem_span_of_eval_eq_zero (R R' D E ν σ : Type) [CommRing R] [CommRing R'] [CommRing D] [CommRing E]
    (a : R →+* R') (c : Ideal R) [Algebra (R ⧸ c) D] (χ : R' →+* E) (ψ : D →+* E) (ζ : ν → D)
    (F : σ → MvPolynomial ν R)
    (hsurj : Function.Surjective (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D))
    (hker : RingHom.ker (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D) =
      Ideal.span (Set.range fun s ↦ MvPolynomial.map (Ideal.Quotient.mk c) (F s)))
    (hpo : IsPushout (CommRingCat.ofHom ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)))
      (CommRingCat.ofHom a) (CommRingCat.ofHom ψ) (CommRingCat.ofHom χ))
    (G : MvPolynomial ν R') (hG : MvPolynomial.eval₂ χ (fun s ↦ ψ (ζ s)) G = 0) :
    G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ⊔
      (c.map a).map (MvPolynomial.C : R' →+* MvPolynomial ν R') := by
  classical
  set J : Ideal (MvPolynomial ν R') := Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ⊔
      (c.map a).map (MvPolynomial.C : R' →+* MvPolynomial ν R') with hJ
  let mkJ : MvPolynomial ν R' →+* MvPolynomial ν R' ⧸ J := Ideal.Quotient.mk J
  have hc : ∀ r ∈ c, (mkJ.comp ((MvPolynomial.C : R' →+* MvPolynomial ν R').comp a)) r = 0 := by
    intro r hr
    simp only [RingHom.comp_apply, mkJ]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hr))
  let base : R ⧸ c →+* MvPolynomial ν R' ⧸ J :=
    Ideal.Quotient.lift c (mkJ.comp ((MvPolynomial.C : R' →+* MvPolynomial ν R').comp a)) hc
  let φ : MvPolynomial ν (R ⧸ c) →+* MvPolynomial ν R' ⧸ J :=
    MvPolynomial.eval₂Hom base (fun s ↦ mkJ (MvPolynomial.X s))
  have hφC : ∀ r : R, φ (MvPolynomial.C (Ideal.Quotient.mk c r)) = mkJ (MvPolynomial.C (a r)) := by
    intro r
    simp [φ, base]
  have hφmap : ∀ P : MvPolynomial ν R,
      φ (MvPolynomial.map (Ideal.Quotient.mk c) P) = mkJ (MvPolynomial.map a P) := by
    intro P
    have h : φ.comp (MvPolynomial.map (Ideal.Quotient.mk c)) = mkJ.comp (MvPolynomial.map a) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp only [RingHom.comp_apply, MvPolynomial.map_C]
        exact hφC r
      · intro s
        simp [φ]
    exact RingHom.congr_fun h P
  let q : MvPolynomial ν (R ⧸ c) →+* D := (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D)
  have hkerφ : RingHom.ker q ≤ RingHom.ker φ := by
    have hq : RingHom.ker q = Ideal.span (Set.range fun s ↦ MvPolynomial.map (Ideal.Quotient.mk c) (F s)) := by
      rw [← hker]; rfl
    rw [hq, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, hφmap, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.subset_span ⟨s, rfl⟩)
  let dA : D →+* MvPolynomial ν R' ⧸ J :=
    q.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨φ, hkerφ⟩
  have hdA : ∀ p, dA (q p) = φ p := fun p =>
    RingHom.liftOfRightInverse_comp_apply q _ _ ⟨φ, hkerφ⟩ p
  have hqX : ∀ s, q (MvPolynomial.X s) = ζ s := fun s => by simp [q]
  have hqC : ∀ x : R ⧸ c, q (MvPolynomial.C x) = algebraMap (R ⧸ c) D x := fun x => by
    simp [q]
  have w : CommRingCat.ofHom ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)) ≫ CommRingCat.ofHom dA =
      CommRingCat.ofHom a ≫ CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R')) := by
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [← hqC, hdA, hφC]
  let desc := hpo.desc (CommRingCat.ofHom dA) (CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R'))) w
  have hinl : ∀ x : D, desc.hom (ψ x) = dA x := fun x => by
    have := congrArg (fun f => f.hom x) (hpo.inl_desc (CommRingCat.ofHom dA)
      (CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R'))) w)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
    exact this
  have hinr : ∀ x : R', desc.hom (χ x) = mkJ (MvPolynomial.C x) := fun x => by
    have := congrArg (fun f => f.hom x) (hpo.inr_desc (CommRingCat.ofHom dA)
      (CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R'))) w)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
    exact this
  have hΦ : desc.hom.comp (MvPolynomial.eval₂Hom χ (fun s ↦ ψ (ζ s))) = mkJ := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact hinr x
    · intro s
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      rw [hinl, ← hqX, hdA]
      simp [φ]
  have h0 : mkJ G = 0 := by
    rw [← hΦ, RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, hG, map_zero]
  exact (Ideal.Quotient.eq_zero_iff_mem).1 h0

end GlobalTheory.PinchKernel
end
