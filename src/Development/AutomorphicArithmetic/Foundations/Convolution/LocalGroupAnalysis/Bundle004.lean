module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.Bundle001
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle006
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle004
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle006
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle025
public import GroundTheory.AutomorphicForms.StableConjCyclic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle053
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

section

open PositivityTheory.Rg.Tf.Geo
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc
open scoped NumberField.AdeleRing TensorProduct

section
variable {F E : Type} [Field F] [Field E] [Algebra F E]

private theorem sum_map_tensor [FiniteDimensional F E] [IsGalois F E] {A : Type} [CommRing A] [Algebra F A]
    (t : E ⊗[F] A) :
    ∑ τ : E ≃ₐ[F] E, Algebra.TensorProduct.map (τ : E →ₐ[F] E) (AlgHom.id F A) t =
      (1 : E) ⊗ₜ[F] (TensorProduct.lid F A (LinearMap.rTensor A (Algebra.trace F E) t)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l a =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, LinearMap.rTensor_tmul,
      TensorProduct.lid_tmul, AlgHom.coe_coe]
    have h : ∑ τ : E ≃ₐ[F] E, ((τ : E →ₐ[F] E) : E → E) l = algebraMap F E (Algebra.trace F E l) :=
      (trace_eq_sum_automorphisms l).symm
    rw [← TensorProduct.sum_tmul, h, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add a b ha hb =>
    simp only [map_add (f := _), Finset.sum_add_distrib, ha, hb, TensorProduct.tmul_add]

private theorem map_mul_tensor {A : Type} [CommRing A] [Algebra F A] (τ τ' : E ≃ₐ[F] E) (t : E ⊗[F] A) :
    Algebra.TensorProduct.map ((τ * τ' : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F A) t =
      Algebra.TensorProduct.map (τ : E →ₐ[F] E) (AlgHom.id F A)
        (Algebra.TensorProduct.map (τ' : E →ₐ[F] E) (AlgHom.id F A) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => simp [Algebra.TensorProduct.map_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

private theorem fixed_tensor [FiniteDimensional F E] [IsGalois F E] {A : Type} [CommRing A] [Algebra F A]
    (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) (T : E ⊗[F] A)
    (h : Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A) T = T) [CharZero F] :
    ∃ a : A, (1 : E) ⊗ₜ[F] a = T := by
  have hpow : ∀ k : ℕ, Algebra.TensorProduct.map ((σ ^ k : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F A) T = T := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero]
      have : ((1 : E ≃ₐ[F] E) : E →ₐ[F] E) = AlgHom.id F E := rfl
      rw [this, Algebra.TensorProduct.map_id]
      rfl
    | succ k ih => rw [pow_succ, map_mul_tensor, h, ih]
  have hall : ∀ τ : E ≃ₐ[F] E, Algebra.TensorProduct.map (τ : E →ₐ[F] E) (AlgHom.id F A) T = T := by
    intro τ
    obtain ⟨k, rfl⟩ := (mem_powers_iff_mem_zpowers).2 (hσ τ)
    exact hpow k
  have hs := sum_map_tensor (F := F) (E := E) T
  simp only [hall, Finset.sum_const, Finset.card_univ] at hs
  have hc : ((Fintype.card (E ≃ₐ[F] E) : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨((Fintype.card (E ≃ₐ[F] E) : ℕ) : F)⁻¹ • TensorProduct.lid F A (LinearMap.rTensor A (Algebra.trace F E) T), ?_⟩
  rw [TensorProduct.tmul_smul, ← hs, ← Nat.cast_smul_eq_nsmul F, smul_smul, inv_mul_cancel₀ hc, one_smul]
end

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem fixed_adele [IsGalois F E] (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ)
    (y : 𝔸[E]) (hy : galAd σ y = y) : ∃ a, adeleMap F E a = y := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h1 : Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F]) ((adeleTensorEquiv F E).symm y) =
      (adeleTensorEquiv F E).symm y := by
    apply (adeleTensorEquiv F E).injective
    rw [AlgEquiv.apply_symm_apply]
    exact hy
  obtain ⟨a, ha⟩ := fixed_tensor σ hσ _ h1
  refine ⟨a, ?_⟩
  have := congrArg (adeleTensorEquiv F E) ha
  rwa [AlgEquiv.apply_symm_apply, adeleTensorEquiv_tmul, map_one, one_mul] at this

private theorem galAd_adeleMap (σ : E ≃ₐ[F] E) (a : 𝔸[F]) : galAd σ (adeleMap F E a) = adeleMap F E a := by
  change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
    ((adeleTensorEquiv F E).symm (adeleMap F E a))) = _
  rw [adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul, map_one, map_one, one_mul]
  rfl

private theorem fixed_mat [IsGalois F E] (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {n : ℕ}
    (y : AdelicGLn.AdelicGL E n) (hy : mapGL n (galAd σ) y = y) :
    ∃ M : Matrix (Fin n) (Fin n) 𝔸[F], M.map (adeleMap F E) = (y : Matrix (Fin n) (Fin n) 𝔸[E]) := by
  have : ∀ i j, ∃ a, adeleMap F E a = (y : Matrix (Fin n) (Fin n) 𝔸[E]) i j := fun i j =>
    fixed_adele σ hσ _ (congrArg (fun u : AdelicGLn.AdelicGL E n => (u : Matrix (Fin n) (Fin n) 𝔸[E]) i j) hy)
  choose M hM using this
  exact ⟨Matrix.of M, Matrix.ext hM⟩
end

theorem UpperTheory.ConvolutionTheory.G.galois_fixed_adelic_matrices_descend :
    N3 := by
  intro F E _ _ _ _ _ _ σ hσ n hn δ γ hγ hN x
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hp : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank F E = 1 := by
    rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
  have hfix : sigmaGL σ (incl γ : GL (Fin n) E) = incl γ := by
    ext i j
    exact σ.commutes _
  have hδ : δ * incl γ = incl γ * δ := by
    have h := map_twNorm_of_pow_eq_one (sigmaGL σ) hp δ
    change sigmaGL σ (normGL σ δ) = δ⁻¹ * normGL σ δ * δ at h
    rw [hN, hfix] at h
    calc δ * incl γ = δ * (δ⁻¹ * incl γ * δ) := by rw [← h]
      _ = incl γ * δ := by group
  obtain ⟨-, hmapd, -⟩ := UpperTheory.adelicGL_galois_baseChange_diagonal_compat F E σ n
  have hDΓ : AdelicGLn.diagonal E n δ * AdelicGLn.diagonal E n (incl γ) =
      AdelicGLn.diagonal E n (incl γ) * AdelicGLn.diagonal E n δ := by
    rw [← map_mul, ← map_mul, hδ]
  have hC : ∀ s t : AdelicGLn.AdelicGL E n, s * AdelicGLn.diagonal E n (incl γ) = AdelicGLn.diagonal E n (incl γ) * s →
      t * AdelicGLn.diagonal E n (incl γ) = AdelicGLn.diagonal E n (incl γ) * t → s * t = t * s := by
    intro s t hs ht
    have hD : ((AdelicGLn.diagonal E n (incl γ) : AdelicGLn.AdelicGL E n) : Matrix (Fin n) (Fin n) 𝔸[E]) =
        (γ : Matrix (Fin n) (Fin n) F).map ((algebraMap E 𝔸[E]).comp (algebraMap F E)) := by
      ext a b
      rfl
    have hs' : (s : Matrix (Fin n) (Fin n) 𝔸[E]) * (γ : Matrix (Fin n) (Fin n) F).map ((algebraMap E 𝔸[E]).comp (algebraMap F E)) =
        (γ : Matrix (Fin n) (Fin n) F).map ((algebraMap E 𝔸[E]).comp (algebraMap F E)) * (s : Matrix (Fin n) (Fin n) 𝔸[E]) := by
      rw [← hD]
      exact congrArg Units.val hs
    have ht' : (t : Matrix (Fin n) (Fin n) 𝔸[E]) * (γ : Matrix (Fin n) (Fin n) F).map ((algebraMap E 𝔸[E]).comp (algebraMap F E)) =
        (γ : Matrix (Fin n) (Fin n) F).map ((algebraMap E 𝔸[E]).comp (algebraMap F E)) * (t : Matrix (Fin n) (Fin n) 𝔸[E]) := by
      rw [← hD]
      exact congrArg Units.val ht
    exact Units.ext (UpperTheory.centralizer_commutative_of_separable_charpoly F 𝔸[E] _ n _ hγ _ _ hs' ht')
  have hinjM : Function.Injective (fun M : Matrix (Fin n) (Fin n) 𝔸[F] => M.map (adeleMap F E)) :=
    Matrix.map_injective adeleMap_injective
  have hinjG : Function.Injective (mapGL n (adeleMap F E) : AdelicGLn.AdelicGL F n → AdelicGLn.AdelicGL E n) := fun a b h =>
    Units.ext (hinjM (congrArg Units.val h))
  constructor
  · intro hx
    have h1 := UpperTheory.twNorm_conj_diagonal_eq_conj_normGL F E σ n δ x
    have h0 := UpperTheory.twNorm_conj_diagonal_eq_conj_normGL F E σ n δ 1
    rw [hx] at h1
    simp only [inv_one, one_mul, map_one, mul_one] at h0
    rw [h0, hN] at h1
    have hcom : x * AdelicGLn.diagonal E n (incl γ) = AdelicGLn.diagonal E n (incl γ) * x := by
      calc x * AdelicGLn.diagonal E n (incl γ) = x * (x⁻¹ * AdelicGLn.diagonal E n (incl γ) * x) := by rw [← h1]
        _ = AdelicGLn.diagonal E n (incl γ) * x := by group
    have hxD := hC x _ hcom hDΓ
    have hθ : mapGL n (galAd σ) x = x := by
      calc mapGL n (galAd σ) x = (AdelicGLn.diagonal E n δ)⁻¹ * x * (x⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) x) := by group
        _ = (AdelicGLn.diagonal E n δ)⁻¹ * (x * AdelicGLn.diagonal E n δ) := by rw [hx, mul_assoc]
        _ = x := by rw [hxD]; group
    have hθ' : mapGL n (galAd σ) x⁻¹ = x⁻¹ := by rw [map_inv, hθ]
    obtain ⟨M, hM⟩ := fixed_mat σ hσ x hθ
    obtain ⟨N, hN'⟩ := fixed_mat σ hσ x⁻¹ hθ'
    have hMN : M * N = 1 := hinjM (by
      change (M * N).map (adeleMap F E) = (1 : Matrix (Fin n) (Fin n) 𝔸[F]).map (adeleMap F E)
      rw [Matrix.map_mul, hM, hN', Matrix.map_one _ (map_zero _) (map_one _)]
      exact congrArg Units.val (mul_inv_cancel x))
    have hNM : N * M = 1 := hinjM (by
      change (N * M).map (adeleMap F E) = (1 : Matrix (Fin n) (Fin n) 𝔸[F]).map (adeleMap F E)
      rw [Matrix.map_mul, hM, hN', Matrix.map_one _ (map_zero _) (map_one _)]
      exact congrArg Units.val (inv_mul_cancel x))
    have he : mapGL n (adeleMap F E) (⟨M, N, hMN, hNM⟩ : AdelicGLn.AdelicGL F n) = x := Units.ext hM
    refine ⟨⟨M, N, hMN, hNM⟩, hinjG ?_, he.symm⟩
    rw [map_mul, map_mul, hmapd, he]
    exact hcom
  · rintro ⟨t, ht, rfl⟩
    have hcomm : mapGL n (adeleMap F E) t * AdelicGLn.diagonal E n (incl γ) =
        AdelicGLn.diagonal E n (incl γ) * mapGL n (adeleMap F E) t := by
      rw [← hmapd, ← map_mul, ← map_mul, ht]
    have hθ : mapGL n (galAd σ) (mapGL n (adeleMap F E) t) = mapGL n (adeleMap F E) t :=
      Units.ext (Matrix.ext fun i j => galAd_adeleMap σ _)
    rw [hθ, mul_assoc, ← hC _ _ hcomm hDΓ]
    group
end

section

open PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Loc Polynomial

private theorem exists_matrix_charpoly {k : Type} [Field k] (P : k[X]) (hP : P.Monic) (n : ℕ)
    (hn : P.natDegree = n) : ∃ M : Matrix (Fin n) (Fin n) k, M.charpoly = P := by
  subst hn
  have hP0 : P ≠ 0 := hP.ne_zero
  have hdim : (AdjoinRoot.powerBasis hP0).dim = P.natDegree := AdjoinRoot.powerBasis_dim hP0
  refine ⟨Matrix.reindex (finCongr hdim) (finCongr hdim)
    (Algebra.leftMulMatrix (AdjoinRoot.powerBasis hP0).basis (AdjoinRoot.powerBasis hP0).gen), ?_⟩
  rw [Matrix.charpoly_reindex, charpoly_leftMulMatrix, AdjoinRoot.minpoly_powerBasis_gen hP0]
  simp [hP.leadingCoeff]

theorem UpperTheory.ConvolutionTheory.G.monic_polynomial_is_matrix_charpoly :
    N1 := by
  intro k E _ _ _ _ _ _ σ hgen n δ hreg
  obtain ⟨P, hP⟩ := charpoly_normGL_lifts σ hgen δ
  have hPm : P.Monic := Polynomial.monic_of_injective (algebraMap k E).injective
    (by rw [hP]; exact Matrix.charpoly_monic _)
  have hdeg : P.natDegree = n := by
    rw [← Polynomial.natDegree_map (f := algebraMap k E), hP, Matrix.charpoly_natDegree_eq_dim]
    simp
  obtain ⟨M, hM⟩ := exists_matrix_charpoly P hPm n hdeg
  have hMc : (M.map (algebraMap k E)).charpoly = ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly := by
    rw [Matrix.charpoly_map, hM, hP]
  have hdetE : (M.map (algebraMap k E)).det = ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, Matrix.det_eq_sign_charpoly_coeff, hMc]
  have hNu : IsUnit ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (normGL σ δ).isUnit
  have hdet : IsUnit M.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [← hdetE] at hNu
    have e : (M.map (algebraMap k E)).det = algebraMap k E M.det := ((algebraMap k E).map_det M).symm
    rw [e, h0, map_zero] at hNu
    exact not_isUnit_zero hNu
  let γ : GL (Fin n) k := Matrix.nonsingInvUnit M hdet
  have hγ : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = M.map (algebraMap k E) := rfl
  obtain ⟨x, hx⟩ := (UpperTheory.ConvolutionTheory.D.conjSep E E n _ hreg).1 ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
    (by rw [hγ]; exact hMc)
  have hx' : normGL σ δ * x = x * incl γ := Units.ext hx
  refine ⟨x, γ, ?_⟩
  have hℓ : σ ^ Module.finrank k E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, hℓ, sigmaGL_one]
  have h := twNorm_twConj_of_pow_eq_one (sigmaGL σ) hθ x δ
  change twNorm (sigmaGL σ) (Module.finrank k E) (twConj (sigmaGL σ) x δ) = incl γ
  rw [h]
  change x⁻¹ * normGL σ δ * x = incl γ
  rw [mul_assoc, hx', inv_mul_cancel_left]
end

section

open PositivityTheory.Rg.Tf.Geo

open PositivityTheory.Rg.Tf.Loc in
private theorem nm_eq_normGL {k E : Type} [Field k] [Field E] [Algebra k E] (σ : E ≃ₐ[k] E) (n q : ℕ)
    (d : GL (Fin n) E) : UpperTheory.ConvolutionTheory.D.nm σ q d = twNorm (sigmaGL σ) q d := by
  unfold UpperTheory.ConvolutionTheory.D.nm twNorm
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [← sigmaGL_pow]
  rfl

open PositivityTheory.Rg.Tf.Loc in
theorem UpperTheory.ConvolutionTheory.G.nm_agrees_with_twisted_norm_sigmaGL :
    N2 := by
  intro k E _ _ _ _ _ _ σ hσ n
  refine ⟨?_, ?_⟩
  · intro δ δ' γ hγ h1 h2
    have hg := UpperTheory.ConvolutionTheory.D.galField k E σ hσ
    have e : ∀ d : GL (Fin n) E, UpperTheory.ConvolutionTheory.D.nm σ (Module.finrank k E) d = normGL σ d :=
      fun d => nm_eq_normGL σ n _ d
    have hsep : (UpperTheory.ConvolutionTheory.D.cp (UpperTheory.ConvolutionTheory.D.nm σ (Module.finrank k E) δ)).Separable := by
      rw [e, h1]
      have hm : UpperTheory.ConvolutionTheory.D.cp (incl γ : GL (Fin n) E) =
          ((γ : Matrix (Fin n) (Fin n) k).charpoly).map (algebraMap k E) := by
        rw [← Matrix.charpoly_map]
        rfl
      rw [hm]
      exact hγ.map
    obtain ⟨x, hx⟩ := UpperTheory.ConvolutionTheory.D.nmInj k E σ _ hg n δ δ' hsep (by rw [e, e, h1, h2])
    exact ⟨x, hx⟩
  · intro γ γ' hγ hc
    obtain ⟨x, hx⟩ := (UpperTheory.ConvolutionTheory.D.conjSep k k n (γ : Matrix (Fin n) (Fin n) k) hγ).1 γ' hc.symm
    have hx' : γ * x = x * γ' := Units.ext hx
    refine ⟨x, ?_⟩
    rw [mul_assoc, hx', inv_mul_cancel_left]
end

section

open PositivityTheory.Rg.Tf.Geo

private theorem exists_krylov_det_ne_zero {k : Type*} [Field k] [Infinite k] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) k) (h : M.charpoly.Separable) :
    ∃ v : Fin n → k, (GroundTheory.Automorphic.krylov M v).det ≠ 0 := by
  have hs : (Matrix.toLin' M).charpoly.Separable := by rwa [Matrix.charpoly_toLin']
  obtain ⟨w, hw⟩ := GroundTheory.Automorphic.exists_linearIndependent_pow_apply _ hs
  rw [Module.finrank_fin_fun] at hw
  refine ⟨w, ?_⟩
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.linearIndependent_cols_iff_isUnit]
  have hcol : (GroundTheory.Automorphic.krylov M w).col =
      fun j : Fin n => (Matrix.toLin' M ^ (j : ℕ)) w := by
    ext1 j
    rw [GroundTheory.Automorphic.krylov_col, ← Matrix.toLin'_pow, Matrix.toLin'_apply]
  rw [hcol]
  exact hw

private theorem isClosed_charpoly_eq {k : Type*} [NontriviallyNormedField k] [Infinite k] {n : ℕ}
    (P : Polynomial k) : IsClosed {g : GL (Fin n) k | (g : Matrix (Fin n) (Fin n) k).charpoly = P} := by
  have : {g : GL (Fin n) k | (g : Matrix (Fin n) (Fin n) k).charpoly = P} =
      ⋂ a : k, {g : GL (Fin n) k | (Matrix.scalar (Fin n) a - (g : Matrix (Fin n) (Fin n) k)).det = P.eval a} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro rfl a
      rw [Matrix.eval_charpoly]
    · intro h
      apply Polynomial.funext
      intro a
      rw [Matrix.eval_charpoly]
      exact h a
  rw [this]
  refine isClosed_iInter fun a => isClosed_eq ?_ continuous_const
  exact (continuous_const.sub Units.continuous_val).matrix_det

private theorem continuous_krylov {k : Type*} [NontriviallyNormedField k] {n : ℕ} (v : Fin n → k) :
    Continuous fun g : GL (Fin n) k => GroundTheory.Automorphic.krylov (g : Matrix (Fin n) (Fin n) k) v := by
  refine continuous_matrix fun i j => ?_
  simp only [GroundTheory.Automorphic.krylov, Matrix.of_apply]
  exact (continuous_apply i).comp (((Units.continuous_val.pow _)).matrix_mulVec continuous_const)

theorem UpperTheory.ConvolutionTheory.G.p1_holds :
    P1 :=
  _root_.UpperTheory.Reformulated.B.ProjectiveLineOf.p1_holds
end

section

open PositivityTheory.Rg.Tf.Geo
open MeasureTheory
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.G

section
variable {X T : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
  [LocallyCompactSpace T] [T2Space T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]

private theorem lintegral_swap_norm (μ : Measure X) [μ.IsHaarMeasure] (ν : Measure T) [ν.IsHaarMeasure]
    [ν.IsInvInvariant] (i : T →* X) (hi : Continuous i) {a b Ψ : X → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b)
    (hΨ : Measurable Ψ) (hinv : ∀ t x, Ψ (i t * x) = Ψ x) (hA : ∀ x, ∫⁻ t, a (i t * x) ∂ν = 1)
    (hB : ∀ x, ∫⁻ t, b (i t * x) ∂ν = 1) :
    ∫⁻ x, Ψ x * a x ∂μ = ∫⁻ x, Ψ x * b x ∂μ :=
  _root_.UpperTheory.Reformulated.B.Qf2.lintegral_swap_norm μ ν i hi ha hb hΨ hinv hA hB

private theorem ae_lt_top_norm (μ : Measure X) [μ.IsHaarMeasure] (ν : Measure T) [ν.IsHaarMeasure]
    (i : T →* X) (hi : Continuous i) {a : X → ℝ≥0∞} (ha : Measurable a) (hA : ∀ x, ∫⁻ t, a (i t * x) ∂ν = 1) :
    ∀ᵐ x ∂μ, a x < ⊤ := by
  have him : Measurable i := hi.measurable
  have hS : MeasurableSet (a ⁻¹' {⊤}) := ha (measurableSet_singleton _)
  set c : X → ℝ≥0∞ := (a ⁻¹' {⊤}).indicator 1 with hc
  have hcm : Measurable c := measurable_one.indicator hS
  have hm : Measurable (fun p : X × T => i p.2 * p.1) := (him.comp measurable_snd).mul measurable_fst
  have hu : Measurable (Function.uncurry fun (x : X) (t : T) => c (i t * x)) := hcm.comp hm
  have h0 : ∫⁻ x, ∫⁻ t, c (i t * x) ∂ν ∂μ = 0 := by
    have : ∀ x, ∫⁻ t, c (i t * x) ∂ν = 0 := by
      intro x
      have hf : ∀ᵐ t ∂ν, a (i t * x) < ⊤ :=
        ae_lt_top (ha.comp (him.mul_const x)) (by rw [hA x]; exact ENNReal.one_ne_top)
      have hcx : Measurable (fun t => c (i t * x)) := hcm.comp (him.mul_const x)
      rw [lintegral_eq_zero_iff hcx]
      filter_upwards [hf] with t ht
      simp [hc, ht.ne]
    simp [this]
  have h1 : ∫⁻ x, ∫⁻ t, c (i t * x) ∂ν ∂μ = μ (a ⁻¹' {⊤}) * ν Set.univ := by
    rw [lintegral_lintegral_swap hu.aemeasurable]
    have : ∀ t, ∫⁻ x, c (i t * x) ∂μ = μ (a ⁻¹' {⊤}) := by
      intro t
      rw [lintegral_mul_left_eq_self c (i t), hc, lintegral_indicator_one hS]
    simp [this]
  rw [h1] at h0
  have hν : ν Set.univ ≠ 0 := (Measure.measure_univ_pos.mpr (NeZero.ne ν)).ne'
  have hμ : μ (a ⁻¹' {⊤}) = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h hν
  have : ∀ᵐ x ∂μ, x ∉ a ⁻¹' {⊤} := measure_eq_zero_iff_ae_notMem.mp hμ
  filter_upwards [this] with x hx
  exact lt_top_iff_ne_top.mpr hx

private theorem lintegral_ofReal_toReal (μ : Measure X) {a : X → ℝ≥0∞} (hfin : ∀ᵐ x ∂μ, a x < ⊤) (c : X → ℝ) :
    ∫⁻ x, ENNReal.ofReal (c x * (a x).toReal) ∂μ = ∫⁻ x, ENNReal.ofReal (c x) * a x ∂μ := by
  refine lintegral_congr_ae ?_
  filter_upwards [hfin] with x hx
  rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]

private theorem real_eq (μ : Measure X) [μ.IsHaarMeasure] (ν : Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant]
    (i : T →* X) (hi : Continuous i) {a b : X → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b)
    (hA : ∀ x, ∫⁻ t, a (i t * x) ∂ν = 1) (hB : ∀ x, ∫⁻ t, b (i t * x) ∂ν = 1) {g : X → ℝ} (hg : Measurable g)
    (hinv : ∀ t x, g (i t * x) = g x) (h1 : Integrable (fun x => g x * (a x).toReal) μ)
    (h2 : Integrable (fun x => g x * (b x).toReal) μ) :
    ∫ x, g x * (a x).toReal ∂μ = ∫ x, g x * (b x).toReal ∂μ := by
  have fa := ae_lt_top_norm μ ν i hi ha hA
  have fb := ae_lt_top_norm μ ν i hi hb hB
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part h1,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part h2]
  simp only [← neg_mul]
  rw [lintegral_ofReal_toReal μ fa g, lintegral_ofReal_toReal μ fa (fun x => - g x),
    lintegral_ofReal_toReal μ fb g, lintegral_ofReal_toReal μ fb (fun x => - g x),
    lintegral_swap_norm μ ν i hi ha hb hg.ennreal_ofReal (fun t x => by rw [hinv]) hA hB,
    lintegral_swap_norm μ ν i hi ha hb (Ψ := fun x => ENNReal.ofReal (- g x)) hg.neg.ennreal_ofReal
      (fun t x => by rw [hinv]) hA hB]

private theorem integrable_mul_toReal (μ : Measure X) {Φ : X → ℂ} {a : X → ℝ≥0∞} (hΦ : Measurable Φ)
    (ha : Measurable a) (hf : ∫⁻ x, ‖Φ x‖ₑ * a x ∂μ < ⊤) :
    Integrable (fun x => Φ x * ((a x).toReal : ℂ)) μ := by
  refine ⟨(hΦ.mul (Complex.measurable_ofReal.comp ha.ennreal_toReal)).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hf
  rw [enorm_mul]
  gcongr
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

end

end UpperTheory.ConvolutionTheory.G

theorem UpperTheory.ConvolutionTheory.G.isUnit_last_join :
    Q1 := by
  intro X G T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ u i hu hi Φ ρ hΦ hinv hn hfin
  have hex : ∃ ρ, IsNormAlong u (fun t => u (i t)) ν ρ := ⟨ρ, hn⟩
  unfold quotInt
  rw [dite_eq_left hex]
  have h0 := hex.choose_spec
  set ρ₀ := hex.choose
  have ha : Measurable (fun x => ρ (u x)) := hn.1.comp hu
  have hb : Measurable (fun x => ρ₀ (u x)) := h0.1.comp hu
  have hA : ∀ x, ∫⁻ t, ρ (u (i t * x)) ∂ν = 1 := fun x => by simpa [map_mul] using hn.2 x
  have hB : ∀ x, ∫⁻ t, ρ₀ (u (i t * x)) ∂ν = 1 := fun x => by simpa [map_mul] using h0.2 x
  have hfin' : ∫⁻ x, ‖Φ x‖ₑ * ρ₀ (u x) ∂μ < ⊤ := by
    rw [← lintegral_swap_norm μ ν i hi ha hb hΦ.enorm (fun t x => by rw [hinv]) hA hB]
    exact hfin
  have h1 := integrable_mul_toReal μ hΦ ha hfin
  have h2 := integrable_mul_toReal μ hΦ hb hfin'
  have hre : ∀ f : _ → ℂ, Integrable f μ → (∫ x, f x ∂μ).re = ∫ x, (f x).re ∂μ :=
    fun f hf => (Complex.reCLM.integral_comp_comm hf).symm
  have him : ∀ f : _ → ℂ, Integrable f μ → (∫ x, f x ∂μ).im = ∫ x, (f x).im ∂μ :=
    fun f hf => (Complex.imCLM.integral_comp_comm hf).symm
  apply Complex.ext
  · rw [hre _ h1, hre _ h2]
    simp only [Complex.re_mul_ofReal]
    refine (real_eq μ ν i hi hb ha hB hA (Complex.measurable_re.comp hΦ) (fun t x => by simp [hinv]) ?_ ?_)
    · simpa [Complex.re_mul_ofReal] using h2.re
    · simpa [Complex.re_mul_ofReal] using h1.re
  · rw [him _ h1, him _ h2]
    simp only [Complex.im_mul_ofReal]
    refine (real_eq μ ν i hi hb ha hB hA (Complex.measurable_im.comp hΦ) (fun t x => by simp [hinv]) ?_ ?_)
    · simpa [Complex.im_mul_ofReal] using h2.im
    · simpa [Complex.im_mul_ofReal] using h1.im
end
