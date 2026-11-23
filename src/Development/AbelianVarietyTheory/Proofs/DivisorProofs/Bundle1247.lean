module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle183
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle166
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetIndicatorThetaTorsionTranslates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TwTraceForm

theorem phi_transpose (a : ℕ) (L : Type) [Field L] :
    (GlobalTheory.Tw.Phi a L)ᵀ = (-1 : L) ^ (a - 1) • GlobalTheory.Tw.Phi a L :=
  (GlobalTheory.antidiag_twisted_norm L (RingEquiv.refl L) (fun _ => rfl) a (GlobalTheory.Tw.Phi a L) (by
    ext i j
    simp only [GlobalTheory.Tw.Phi, Matrix.of_apply]
    have : ((i : ℕ) + (j : ℕ) + 1 = a) ↔ j = i.rev := by
      rw [Fin.ext_iff, Fin.val_rev]; omega
    simp only [this])).1

theorem phi_map (a : ℕ) (L : Type) [Field L] (c : L →+* L) :
    (GlobalTheory.Tw.Phi a L).map c = GlobalTheory.Tw.Phi a L := by
  ext i j
  simp only [GlobalTheory.Tw.Phi, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem phi_transpose_mul (a : ℕ) (L : Type) [Field L] :
    (GlobalTheory.Tw.Phi a L)ᵀ * GlobalTheory.Tw.Phi a L = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.CuspRep.Phi_mul_transpose a L)

theorem gram_eq (a : ℕ) (L : Type) [Field L] (δ : GL (Fin a) L) :
    ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = ((δ⁻¹ : GL (Fin a) L).val)ᵀ * GlobalTheory.Tw.Phi a L := by
  have h : (δ.val * GlobalTheory.Tw.Phi a L)⁻¹ = (GlobalTheory.Tw.Phi a L)ᵀ * (δ⁻¹ : GL (Fin a) L).val := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (δ⁻¹ : GL (Fin a) L).val, Units.inv_mul, Matrix.one_mul,
      phi_transpose_mul]
  rw [h, Matrix.transpose_mul, Matrix.transpose_transpose]

theorem gram_mul_transpose (a : ℕ) (L : Type) [Field L] (δ : GL (Fin a) L) :
    ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ * (δ.val * GlobalTheory.Tw.Phi a L)ᵀ = 1 := by
  rw [gram_eq, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (GlobalTheory.Tw.Phi a L),
    GlobalTheory.CuspRep.Phi_mul_transpose, Matrix.one_mul, ← Matrix.transpose_mul, Units.mul_inv,
    Matrix.transpose_one]

theorem gram_norm (a : ℕ) (L : Type) [Field L] (c : L →+* L) (δ : GL (Fin a) L) :
    (((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ)ᵀ * (δ * thetaGL a c δ).val
      = (-1 : L) ^ (a - 1) • (((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ).map c := by
  have hθ : (thetaGL a c δ).val
      = GlobalTheory.Tw.Phi a L * (((δ⁻¹ : GL (Fin a) L).val).map c)ᵀ * (GlobalTheory.Tw.Phi a L)ᵀ := rfl
  rw [gram_eq, Units.val_mul, hθ, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.map_mul, Matrix.transpose_map, phi_map]
  set Φ := GlobalTheory.Tw.Phi a L
  set Di := (δ⁻¹ : GL (Fin a) L).val
  set X := (Di.map c)ᵀ
  calc Φᵀ * Di * (δ.val * (Φ * X * Φᵀ))
      = Φᵀ * (Di * δ.val) * Φ * X * Φᵀ := by
        simp only [Matrix.mul_assoc]
    _ = X * Φᵀ := by
        rw [Units.inv_mul, Matrix.mul_one, phi_transpose_mul, Matrix.one_mul]
    _ = (-1 : L) ^ (a - 1) • (X * Φ) := by
        rw [phi_transpose, Matrix.mul_smul]

theorem form_asym {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (σ : k ≃+* k)
    (hσ : ∀ x, σ (σ x) = x) (S N : Matrix n n k) (ε : k) (h : S.map σ = ε • (Sᵀ * N))
    (u v : n → k) :
    σ (v ⬝ᵥ S *ᵥ (fun j => σ (u j))) = (ε • N *ᵥ u) ⬝ᵥ S *ᵥ (fun j => σ (v j)) := by
  have h1 : σ (v ⬝ᵥ S *ᵥ (fun j => σ (u j))) = (fun j => σ (v j)) ⬝ᵥ S.map σ *ᵥ u := by
    rw [show σ (v ⬝ᵥ S *ᵥ (fun j => σ (u j))) = (σ : k →+* k) (v ⬝ᵥ S *ᵥ (fun j => σ (u j))) from rfl,
      RingHom.map_dotProduct]
    congr 1
    funext i
    rw [Function.comp_apply, RingHom.map_mulVec]
    congr 1
    funext j
    simp [hσ]
  rw [h1, h, Matrix.smul_mulVec, dotProduct_smul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, smul_dotProduct, dotProduct_comm, smul_eq_mul]

end GlobalTheory.TwTraceForm

namespace GlobalTheory.TwTraceForm

theorem exists_trace_form : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → (∀ x, c (c x) = x) → B.g * B.σ B.g = 1 → ∀ (a : ℕ) (Q : L[X]), B.P = Q.map e.symm.toRingHom → Q.Separable → Q.natDegree = a → ∀ δ : GL (Fin a) L, (δ * thetaGL a c δ).val.charpoly = Q → ∃ β : B.Aˣ, B.σ (β : B.A) = β * ((-1) ^ (a - 1) * B.g) ∧ ∃ b : Module.Basis (Fin a) K.E B.A, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = (Matrix.of fun i j => e (B.herm β (b i) (b j))) := by
  intro K B L _ e c hec hcc hg a Q hBP hQs hQd δ hδ
  classical
  let f : L →+* K.E := e.symm.toRingHom
  have hf : ∀ x, f (c x) = K.c (f x) := by
    intro x
    apply e.injective
    show e (e.symm (c x)) = e (K.c (e.symm x))
    rw [hec, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  set G := ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ with hG
  set N := (δ * thetaGL a c δ).val with hN
  set S := G.map f with hS
  set N' := N.map f with hN'
  set ε : K.E := (-1) ^ (a - 1) with hε
  have hεε : ε * ε = 1 := by rw [hε, ← mul_pow]; simp
  have hkey : Sᵀ * N' = ε • S.map K.c := by
    have h0 := congrArg f.mapMatrix (gram_norm a L c δ)
    rw [map_mul] at h0
    simp only [RingHom.mapMatrix_apply] at h0
    rw [Matrix.transpose_map] at h0
    change Sᵀ * N' = _ at h0
    rw [h0]
    ext i j
    simp [f, hf, hε, Matrix.map_apply, Matrix.smul_apply]
    exact hf _
  have hSc : S.map K.c = ε • (Sᵀ * N') := by rw [hkey, smul_smul, hεε, one_smul]
  set Y := ((δ.val * GlobalTheory.Tw.Phi a L)ᵀ).map f with hY
  have hSY : S * Y = 1 := by
    have h0 := congrArg f.mapMatrix (gram_mul_transpose a L δ)
    rw [map_mul, map_one] at h0
    exact h0
  have hsep : (LinearMap.mulLeft K.E B.g).charpoly.Separable := by
    show B.P.Separable
    rw [hBP]; exact hQs.map
  have hchar : (LinearMap.mulLeft K.E B.g).charpoly = (Matrix.toLin' N').charpoly := by
    rw [Matrix.charpoly_toLin', hN', Matrix.charpoly_map, hδ]
    exact hBP
  obtain ⟨ψ, hψ⟩ := GlobalTheory.UnitLemma.PairClass.exists_intertwine K.E B.A (Fin a → K.E)
    (LinearMap.mulLeft K.E B.g) (Matrix.toLin' N') hsep hchar
  have hψ' : ∀ y, ψ (B.g * y) = N' *ᵥ ψ y := fun y => by simpa using hψ y
  have hc1 : ∀ j : Fin a, (fun k => K.c ((Pi.single j (1 : K.E) : Fin a → K.E) k)) = (Pi.single j 1 : Fin a → K.E) := by
    intro j
    funext k
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  let s : B.A → B.A → K.E := fun y z => ψ y ⬝ᵥ S *ᵥ (fun j => K.c (ψ z j))
  have hadd : ∀ x y z, s (x + y) z = s x z + s y z := by
    intro x y z
    simp only [s, map_add (f := _), add_dotProduct]
  have hlin : ∀ (r : K.E) x z, s (r • x) z = r * s x z := by
    intro r x z
    simp only [s, map_smul, smul_dotProduct, smul_eq_mul]
  have hnd : ∀ y, (∀ z, s y z = 0) → y = 0 := by
    intro y hy
    have hv : ψ y ᵥ* S = 0 := by
      funext j
      have h1 := hy (ψ.symm (Pi.single j 1))
      simp only [s, LinearEquiv.apply_symm_apply] at h1
      rw [hc1 j, Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at h1
      exact h1
    have h2 : ψ y = 0 := by
      rw [← Matrix.vecMul_one (ψ y), ← hSY, ← Matrix.vecMul_vecMul, hv, Matrix.zero_vecMul]
    exact ψ.injective (by rw [h2, map_zero])
  have hsym : ∀ y z, K.c (s z y) = s ((-1 : B.A) ^ (a - 1) * B.g * y) z := by
    intro y z
    have hψε : ψ ((-1 : B.A) ^ (a - 1) * B.g * y) = ε • N' *ᵥ ψ y := by
      have h1 : (-1 : B.A) ^ (a - 1) = algebraMap K.E B.A ε := by simp [hε]
      rw [h1, mul_assoc, ← Algebra.smul_def, map_smul, hψ']
    simp only [s]
    rw [hψε]
    exact form_asym K.c K.c_c S N' ε hSc (ψ y) (ψ z)
  obtain ⟨β, hβ, hs⟩ := (GlobalTheory.SesqAsym.sesq_asym K B hg hsep ((-1) ^ (a - 1))
    (neg_one_pow_eq_or B.A (a - 1))).2 s hadd hlin hnd hsym
  refine ⟨β, hβ, (Pi.basisFun K.E (Fin a)).map ψ.symm, ?_⟩
  ext i j
  simp only [Matrix.of_apply, Module.Basis.map_apply, Pi.basisFun_apply]
  rw [← hs]
  simp only [s, LinearEquiv.apply_symm_apply]
  rw [hc1 j, Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply, hS, Matrix.map_apply]
  exact (e.apply_symm_apply _).symm

end GlobalTheory.TwTraceForm
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitLemma.IsometryUnit

theorem isometry_unit : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∀ (a : ℕ) (β β' : B.Aˣ), B.σ (β : B.A) = β * (ε * B.g) → B.σ (β' : B.A) = β' * (ε * B.g) → ∀ b b' : Module.Basis (Fin a) K.E B.A, (∀ i j, B.herm β (b i) (b j) = B.herm β' (b' i) (b' j)) → ∃ t : B.Aˣ, (β' : B.A) = β * (t * B.σ t) := by
  intro K B hs ε hε a β β' hβ hβ' b b' hgram
  have hs' : (LinearMap.mulLeft K.E B.g).charpoly.Separable := hs
  have σsm : ∀ (r : K.E) (y : B.A), B.σ (r • y) = K.c r • B.σ y := by
    intro r y; rw [Algebra.smul_def, map_mul, B.σ_alg, Algebra.smul_def]
  have trσ := GlobalTheory.UnitLemma.PairClass.trace_σ K B
  have addL : ∀ (x u u' v : B.A), B.herm x (u + u') v = B.herm x u v + B.herm x u' v := by
    intro x u u' v; unfold InvAlg.herm; rw [mul_add, add_mul, map_add (f := _)]
  have subL : ∀ (x u u' v : B.A), B.herm x (u - u') v = B.herm x u v - B.herm x u' v := by
    intro x u u' v; unfold InvAlg.herm; rw [mul_sub, sub_mul, map_sub]
  have smulL : ∀ (x : B.A) (r : K.E) (u v : B.A), B.herm x (r • u) v = r * B.herm x u v := by
    intro x r u v; unfold InvAlg.herm; rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]
  have addR : ∀ (x u v v' : B.A), B.herm x u (v + v') = B.herm x u v + B.herm x u v' := by
    intro x u v v'; unfold InvAlg.herm; rw [map_add (f := _), mul_add, map_add (f := _)]
  have smulR : ∀ (x : B.A) (r : K.E) (u v : B.A), B.herm x u (r • v) = K.c r * B.herm x u v := by
    intro x r u v; unfold InvAlg.herm; rw [σsm, mul_smul_comm, map_smul, smul_eq_mul]

  have asym : ∀ (x : B.A), B.σ x = x * (ε * B.g) → ∀ z y, K.c (B.herm x z y) = B.herm x (ε * B.g * y) z := by
    intro x hx z y; unfold InvAlg.herm
    rw [← trσ]; congr 1; simp only [map_mul, B.σ_σ, hx]; ring

  have nd : ∀ x : B.A, (∀ y, Algebra.trace K.E B.A (x * y) = 0) → x = 0 :=
    fun x hx => GlobalTheory.UnitLemma.PairClass.trace_nondeg K.E B.A B.g hs' x hx
  have ndh : ∀ w : B.A, (∀ z, B.herm β w z = 0) → w = 0 := by
    intro w hw
    have h0 : (β : B.A) * w = 0 := nd _ (fun y => by
      have := hw (B.σ y); unfold InvAlg.herm at this; rwa [B.σ_σ] at this)
    have := congrArg (fun z => ((β⁻¹ : B.Aˣ) : B.A) * z) h0
    simpa [← mul_assoc] using this

  let φ : B.A ≃ₗ[K.E] B.A := b'.equiv b (Equiv.refl _)
  have hφb : ∀ i, φ (b' i) = b i := fun i => by simp [φ, Module.Basis.equiv_apply]
  have hφ : ∀ u v, B.herm β (φ u) (φ v) = B.herm β' u v := by
    let F₁ : B.A →ₗ[K.E] B.A →ₛₗ[(K.c : K.E →+* K.E)] K.E :=
      LinearMap.mk₂'ₛₗ (RingHom.id K.E) (K.c : K.E →+* K.E) (fun u v => B.herm β (φ u) (φ v))
        (fun u u' v => by rw [map_add (f := _), addL]) (fun r u v => by rw [map_smul, smulL]; rfl)
        (fun u v v' => by rw [map_add (f := _), addR]) (fun r u v => by rw [map_smul, smulR]; rfl)
    let F₂ : B.A →ₗ[K.E] B.A →ₛₗ[(K.c : K.E →+* K.E)] K.E :=
      LinearMap.mk₂'ₛₗ (RingHom.id K.E) (K.c : K.E →+* K.E) (fun u v => B.herm β' u v)
        (fun u u' v => addL _ _ _ _) (fun r u v => smulL _ _ _ _)
        (fun u v v' => addR _ _ _ _) (fun r u v => smulR _ _ _ _)
    have hF : F₁ = F₂ := LinearMap.ext_basis b' b' (fun i j => by
      simp only [F₁, F₂, LinearMap.mk₂'ₛₗ_apply, hφb]; exact hgram i j)
    intro u v
    have := LinearMap.congr_fun₂ hF u v
    simp only [F₁, F₂, LinearMap.mk₂'ₛₗ_apply] at this
    exact this
  have hcomm : ∀ u, φ (ε * B.g * u) = ε * B.g * φ u := by
    intro u
    rw [← sub_eq_zero]
    apply ndh
    intro z
    obtain ⟨v, rfl⟩ : ∃ v, φ v = z := ⟨φ.symm z, by simp⟩
    rw [subL, hφ, ← asym _ hβ', ← hφ, asym _ hβ, sub_self]
  have hg : ∀ u, φ (B.g * u) = B.g * φ u := by
    intro u
    rcases hε with rfl | rfl
    · simpa using hcomm u
    · have := hcomm u
      simp only [neg_mul, one_mul, map_neg, neg_inj] at this
      exact this
  have hpoly : ∀ q : K.E[X], ∀ u, φ (aeval B.g q * u) = aeval B.g q * φ u := by
    intro q
    induction q using Polynomial.induction_on with
    | C r => intro u; rw [aeval_C, ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
    | add p q hp hq => intro u; rw [map_add (f := _), add_mul, add_mul, map_add (f := _), hp, hq]
    | monomial n r h =>
      intro u
      have e : aeval B.g (C r * X ^ (n + 1)) = aeval B.g (C r * X ^ n) * B.g := by
        simp [pow_succ, mul_assoc]
      rw [e, mul_assoc, h, hg, mul_assoc]
  have hmul : ∀ y, φ y = y * φ 1 := by
    intro y
    obtain ⟨q, rfl⟩ := GlobalTheory.UnitLemma.PairClass.exists_aeval_eq_of_separable B.g hs' y
    simpa using hpoly q 1
  have ht : IsUnit (φ 1) := by
    have := hmul (φ.symm 1)
    rw [LinearEquiv.apply_symm_apply] at this
    exact ⟨⟨φ 1, φ.symm 1, by rw [mul_comm]; exact this.symm, this.symm⟩, rfl⟩
  refine ⟨ht.unit, ?_⟩
  rw [IsUnit.unit_spec]
  rw [← sub_eq_zero]
  apply nd
  intro y
  have h1 := hφ y 1
  rw [hmul y] at h1
  unfold InvAlg.herm at h1
  rw [map_one B.σ, mul_one] at h1
  have h2 : ((β' : B.A) - β * (φ 1 * B.σ (φ 1))) * y = (β' : B.A) * y - β * (y * φ 1) * B.σ (φ 1) := by ring
  rw [h2, map_sub, h1, sub_self]

end GlobalTheory.UnitLemma.IsometryUnit
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

namespace GlobalTheory.IntMatBound

variable (K : UQ) {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (e : K.E ≃+* L)

def boundSub (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (n : ℕ) (m : ℤ) :
    Submodule K.O (Matrix (Fin n) (Fin n) K.E) where
  carrier := {X | ∀ i j, Valued.v (e (X i j)) ≤ WithZero.exp m}
  add_mem' := by
    intro X Y hX hY i j
    simp only [Matrix.add_apply, map_add (f := _)]
    exact Valuation.map_add_le _ (hX i j) (hY i j)
  zero_mem' := by
    intro i j
    simp
  smul_mem' := by
    intro c X hX i j
    simp only [Matrix.smul_apply, Algebra.smul_def, map_mul, Valuation.map_mul]
    have h1 : Valued.v (e (algebraMap K.O K.E c)) ≤ 1 := (he _).1 ⟨c, rfl⟩
    calc Valued.v (e (algebraMap K.O K.E c)) * Valued.v (e (X i j)) ≤ 1 * WithZero.exp m :=
          mul_le_mul' h1 (hX i j)
      _ = WithZero.exp m := one_mul _

theorem exists_bound (x : K.E) : ∃ m : ℤ, Valued.v (e x) ≤ WithZero.exp m := by
  by_cases h : Valued.v (e x) = 0
  · exact ⟨0, by rw [h]; exact zero_le'⟩
  · exact ⟨(Valued.v (e x)).log, (WithZero.exp_log h).ge⟩

theorem exists_unif (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) :
    ∃ ϖ : K.O, ϖ ≠ 0 ∧ Valued.v (e (algebraMap K.O K.E ϖ)) ≤ WithZero.exp (-1) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  refine ⟨ϖ, hϖ.ne_zero, ?_⟩
  set w := Valued.v (e (algebraMap K.O K.E ϖ)) with hw
  have hE : algebraMap K.O K.E ϖ ≠ 0 := by
    intro h0
    exact hϖ.ne_zero (IsFractionRing.injective K.O K.E (by simpa using h0))
  have w0 : w ≠ 0 := by
    rw [hw, Valuation.ne_zero_iff]
    exact (map_ne_zero e).2 hE
  have w1 : w ≤ 1 := (he _).1 ⟨ϖ, rfl⟩
  have wne : w ≠ 1 := by
    intro h1
    have : Valued.v (e (algebraMap K.O K.E ϖ)⁻¹) ≤ 1 := by
      rw [map_inv₀, map_inv₀, ← hw, h1, inv_one]
    obtain ⟨u, hu⟩ := (he _).2 this
    apply hϖ.not_isUnit
    refine IsUnit.of_mul_eq_one (b := u) (IsFractionRing.injective K.O K.E ?_)
    rw [map_mul, hu, map_one, mul_inv_cancel₀ hE]
  have wlt : w < 1 := lt_of_le_of_ne w1 wne
  have hlog : w.log < 0 := by
    rw [← WithZero.exp_lt_exp, WithZero.exp_log w0, WithZero.exp_zero]
    exact wlt
  rw [← WithZero.exp_log w0, WithZero.exp_le_exp]
  omega

end GlobalTheory.IntMatBound

open GlobalTheory.IntMatBound in
theorem GlobalTheory.IntMatBound.isIntegral_iff_bounded : ∀ (K : UQ) {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (e : K.E ≃+* L), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) K.E), IsIntegral K.O M ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j, Valued.v (e ((M ^ k) i j)) ≤ WithZero.exp m := by
  intro K L _ _ e he n M
  constructor
  · intro hM
    obtain ⟨s, hs⟩ := hM.fg_adjoin_singleton
    have hb : ∀ p : s × Fin n × Fin n, ∃ m : ℤ, Valued.v (e ((p.1 : Matrix (Fin n) (Fin n) K.E) p.2.1 p.2.2)) ≤ WithZero.exp m :=
      fun p => exists_bound K e _
    choose f hf using hb
    obtain ⟨m, hm⟩ := (Set.finite_range f).bddAbove
    refine ⟨m, fun k i j => ?_⟩
    have hle : Submodule.span K.O (s : Set (Matrix (Fin n) (Fin n) K.E)) ≤ boundSub K e he n m := by
      rw [Submodule.span_le]
      intro X hX i j
      exact (hf ⟨⟨X, hX⟩, i, j⟩).trans (WithZero.exp_le_exp.2 (hm ⟨_, rfl⟩))
    have hk : M ^ k ∈ Submodule.span K.O (s : Set (Matrix (Fin n) (Fin n) K.E)) := by
      rw [hs]
      exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton K.O M) k
    exact hle hk i j
  · rintro ⟨m, hm⟩
    obtain ⟨ϖ, hϖ0, hϖ⟩ := exists_unif K e he
    have hE : algebraMap K.O K.E ϖ ≠ 0 := by
      intro h0
      exact hϖ0 (IsFractionRing.injective K.O K.E (by simpa using h0))
    set N := m.toNat with hN
    set y : K.E := (algebraMap K.O K.E ϖ)⁻¹ ^ N with hy
    set S : Submodule K.O (Matrix (Fin n) (Fin n) K.E) :=
      Submodule.span K.O (Set.range fun p : Fin n × Fin n => Matrix.single p.1 p.2 y) with hS
    have hmem : ∀ X : Matrix (Fin n) (Fin n) K.E, (∀ i j, Valued.v (e (X i j)) ≤ WithZero.exp m) → X ∈ S := by
      intro X hX
      rw [Matrix.matrix_eq_sum_single X]
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
      have hv : Valued.v (e ((algebraMap K.O K.E ϖ) ^ N * X i j)) ≤ 1 := by
        rw [map_mul, map_pow, Valuation.map_mul, Valuation.map_pow]
        calc Valued.v (e (algebraMap K.O K.E ϖ)) ^ N * Valued.v (e (X i j))
            ≤ WithZero.exp (-1) ^ N * WithZero.exp m := mul_le_mul' (pow_le_pow_left' hϖ N) (hX i j)
          _ = WithZero.exp (N • (-1 : ℤ) + m) := by rw [WithZero.exp_add, WithZero.exp_nsmul]
          _ ≤ WithZero.exp 0 := by
              rw [WithZero.exp_le_exp, nsmul_eq_mul, hN]
              omega
          _ = 1 := WithZero.exp_zero
      obtain ⟨c, hc⟩ := (he _).2 hv
      have : Matrix.single i j (X i j) = c • Matrix.single i j y := by
        rw [Matrix.smul_single, Algebra.smul_def, hc, hy, inv_pow, mul_assoc, mul_comm (X i j), ← mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero _ hE), one_mul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
    have hSfg : S.FG := Submodule.fg_span (Set.finite_range _)
    have hle : Subalgebra.toSubmodule (Algebra.adjoin K.O {M}) ≤ S := by
      rw [Algebra.adjoin_eq_span, Submodule.span_le]
      rintro _ hx
      obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.1 hx
      exact hmem _ (hm k)
    haveI := isNoetherian_of_fg_of_noetherian S hSfg
    haveI := isNoetherian_of_le hle
    have hfg : (Subalgebra.toSubmodule (Algebra.adjoin K.O {M})).FG := Module.Finite.iff_fg.mp inferInstance
    exact IsIntegral.of_mem_of_fg _ hfg M (Algebra.self_mem_adjoin_singleton K.O M)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.sectionsDim_le_add_mul_sectionsDim_cut : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (F : X.Modules) [IsFiniteQC F], ∀ (B M : LB X) (hB : B.IsLB) (hM : M.IsLB) (s t : B.Sec), Mono (cutHom F hB s) → Mono (cutHom (cut F hB s) hB t) → ∀ (j : ℕ) (M' : LB X) (hM' : M'.IsLB), cls M hM = cls M' hM' + j • cls B hB → hdim k (twist F M) 0 ≤ hdim k (twist F M') 0 + j * hdim k (twist (cut F hB s) M) 0 := by
  first | exact @GlobalTheory.SiuChain.hdim_le_add_mul_hdim_cut | exact GlobalTheory.SiuChain.hdim_le_add_mul_hdim_cut | (intros; apply GlobalTheory.SiuChain.hdim_le_add_mul_hdim_cut <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.cosetIndicatorTheta_torsionTranslates : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), X.Ok → s.Ok → StandardLatticesGL3.Crv D cc dl → ∀ (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (L : Submodule (𝓞 X.E) (Sp X.E a)) (L' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b), IsSdLat L → IsSdLat L' → 0 < c → Pres D (TaylorLogMetric.tor0 D cc dl) (s.lat L) (s.lat L') (B.thMoved a b (s.lat L) (s.lat L')) (toHost s fun z => ((ambOf s B χ cD).chiF a b L L')⁻¹ * (ambOf s B χ cD).thInd S L L' c x z) ((c : ℝ) ^ (Module.finrank ℚ X.E * a * b)) := by
  first | exact @GlobalTheory.ColNorms.IndPres.pres_thInd | exact GlobalTheory.ColNorms.IndPres.pres_thInd | (intros; apply GlobalTheory.ColNorms.IndPres.pres_thInd <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

theorem _root_.GlobalTheory.T.characterLineBundle_additive_of_equivariantGenerator : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' N T : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ) (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsAbelianScheme A → IsAbelianScheme A' → IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → M.IsLB → IsEquivGen i q χ M e → IsAdditive M := by
  first | exact @GlobalTheory.CharKer.isAdditive_of_isEquivGen | exact GlobalTheory.CharKer.isAdditive_of_isEquivGen | (intros; apply GlobalTheory.CharKer.isAdditive_of_isEquivGen <;> assumption)
end
