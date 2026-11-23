module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.RepresentationTheory.Semisimple
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle022
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
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
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_semisimple_rep_tpow {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G]
    (ρ : G →* Matrix ι ι ℂ) (h : SS (Set.range ρ)) (n : ℕ) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (r : Representation ℂ G V)
      (b : Module.Basis (Fin n → ι) ℂ V),
      r.IsSemisimpleRepresentation ∧ ∀ g, LinearMap.toMatrix b b (r g) = tpow n (ρ g) := by
  induction n with
  | zero =>
    have hm : ∀ g : G, LinearMap.toMatrix (Pi.basisFun ℂ (Fin 0 → ι)) (Pi.basisFun ℂ (Fin 0 → ι))
        (Representation.trivial ℂ G ((Fin 0 → ι) → ℂ) g) = 1 := by
      intro g
      have : Representation.trivial ℂ G ((Fin 0 → ι) → ℂ) g = LinearMap.id := by
        ext v; simp
      rw [this, LinearMap.toMatrix_id]
    refine ⟨(Fin 0 → ι) → ℂ, inferInstance, inferInstance, Representation.trivial ℂ G _,
      Pi.basisFun ℂ _, ?_, ?_⟩
    · rw [← GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation (Fin 0 → ι) G _ _ (Pi.basisFun ℂ _)]
      intro W _
      obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
      refine ⟨W', ?_, hW'⟩
      rintro _ ⟨g, rfl⟩ v hv
      simpa only [hm, Matrix.one_mulVec] using hv
    · intro g
      rw [hm]
      ext a b
      have : a = b := Subsingleton.elim _ _
      subst this
      simp [tpow]
  | succ n ih =>
    obtain ⟨V, _, _, r, b, hr, hb⟩ := ih
    let r₁ : Representation ℂ G (ι → ℂ) :=
      (Matrix.toLinAlgEquiv' (R := ℂ) (n := ι)).toAlgHom.toMonoidHom.comp ρ
    have h₁ : ∀ g, LinearMap.toMatrix (Pi.basisFun ℂ ι) (Pi.basisFun ℂ ι) (r₁ g) = ρ g := by
      intro g
      change LinearMap.toMatrix (Pi.basisFun ℂ ι) (Pi.basisFun ℂ ι) (Matrix.toLin' (ρ g)) = ρ g
      rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    have hs₁ : r₁.IsSemisimpleRepresentation := by
      rw [← GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation ι G _ _ (Pi.basisFun ℂ _)]
      simpa only [h₁] using h
    haveI : FiniteDimensional ℂ V := Module.Finite.of_basis b
    let e : ι × (Fin n → ι) ≃ (Fin (n + 1) → ι) := Fin.consEquiv fun _ => ι
    refine ⟨(ι → ℂ) ⊗[ℂ] V, inferInstance, inferInstance, r₁.tprod r,
      ((Pi.basisFun ℂ ι).tensorProduct b).reindex e,
      GlobalTheory.T.isSemisimpleRepresentation_tprod_chevalley G _ r₁ V r hs₁ hr, ?_⟩
    intro g
    have ht : LinearMap.toMatrix ((Pi.basisFun ℂ ι).tensorProduct b) ((Pi.basisFun ℂ ι).tensorProduct b)
        ((r₁.tprod r) g) = ρ g ⊗ₖ tpow n (ρ g) := by
      rw [Representation.tprod_apply, TensorProduct.toMatrix_map, h₁, hb]
    ext a c
    have := congrFun (congrFun ht (e.symm a)) (e.symm c)
    rw [LinearMap.toMatrix_apply] at this ⊢
    rw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply, this]
    simp [e, tpow, Fin.prod_univ_succ, Fin.consEquiv, Fin.tail]

theorem ss_tpow_transpose : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)),
    IsPre Γ → SS Γ → ∀ n : ℕ, SS ((fun g => (tpow n g)ᵀ) '' Γ) := by
  intro ι _ _ Γ hΓ hs n
  obtain ⟨G, _, ρ, rfl⟩ := GlobalTheory.T.exists_group_hom_range_eq_of_isPre ι Γ hΓ
  obtain ⟨V, _, _, r, b, hr, hb⟩ := exists_semisimple_rep_tpow ρ hs n
  have h := GlobalTheory.T.isCompletelyReducibleMatrixSet_transpose_image _ _ ((GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation _ G V r b).2 hr)
  simp only [hb] at h
  rw [← Set.range_comp] at h ⊢
  exact h

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.Move

section General

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem fv_mulVec (γ : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    fv F (γ *ᵥ v) = fm F γ *ᵥ fv F v := by
  funext i
  simp only [fv, fm, Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, TensorProduct.tmul_sum]

theorem fv_smul (s : E) (v : Fin n → E) :
    fv F (s • v) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] s : RA F E) • fv F v := by
  funext i
  simp only [fv, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem fv_sub (x y : Fin n → E) : fv F (x - y) = fv F x - fv F y := by
  funext i
  simp [fv, TensorProduct.tmul_sub]

theorem nsmul_cancel {M : ℕ} (hM : 0 < M) {x y : Fin n → RA F E} (h : M • x = M • y) : x = y := by
  have hM' : (M : F) ≠ 0 := by exact_mod_cast hM.ne'
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  have := congrArg (fun z => (M : F)⁻¹ • z) h
  simpa [smul_smul, inv_mul_cancel₀ hM'] using this

end General

section Ideals

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem span_smul_le (s : 𝓞 E) (A B : Submodule (𝓞 E) (Fin n → E)) :
    Ideal.span {s} • A ≤ B ↔ ∀ v ∈ A, s • v ∈ B := by
  rw [Submodule.ideal_span_singleton_smul]
  constructor
  · intro h v hv
    exact h (Submodule.smul_mem_pointwise_smul v _ A hv)
  · intro h x hx
    obtain ⟨v, hv, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact h v hv

theorem exists_nat_coprime (s : 𝓞 E) (N : ℕ)
    (h : ∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → (N : 𝓞 E) ∉ P) :
    ∃ k : ℕ, k.Coprime N ∧ s ∣ (k : 𝓞 E) := by
  set I : Ideal ℤ := (Ideal.span {s}).comap (algebraMap ℤ (𝓞 E)) with hI
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal I).principal
  have haI : a ∈ I := by rw [ha]; exact Submodule.mem_span_singleton_self a
  refine ⟨a.natAbs, ?_, ?_⟩
  · refine Nat.coprime_of_dvd fun p hp hpa hpN => ?_
    have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    haveI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp'.ne_zero).2 hp'
    have hle : I ≤ Ideal.span {(p : ℤ)} := by
      rw [ha]
      exact Ideal.span_singleton_le_span_singleton.2 (Int.natCast_dvd.2 hpa)
    obtain ⟨Q, hQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {(p : ℤ)})
      (Ideal.span {s}) hle
    refine h Q hQp (hQ (Ideal.mem_span_singleton_self s)) ?_
    have : ((N : ℕ) : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
      change ((N : ℕ) : ℤ) ∈ Ideal.under ℤ Q
      rw [hQc, Ideal.mem_span_singleton]; exact_mod_cast hpN
    simpa using this
  · have h1 : s ∣ ((a : ℤ) : 𝓞 E) := by
      have := haI
      rw [hI, Ideal.mem_comap, Ideal.mem_span_singleton] at this
      simpa using this
    have h2 : ((a : ℤ) : 𝓞 E) ∣ ((a.natAbs : ℤ) : 𝓞 E) :=
      map_dvd (Int.castRingHom (𝓞 E)) (Int.dvd_natAbs.2 dvd_rfl)
    rw [Int.cast_natCast] at h2
    exact h1.trans h2

theorem smul_mem_of_dvd {s t : 𝓞 E} (h : s ∣ t) {B : Submodule (𝓞 E) (Fin n → E)} {v : Fin n → E}
    (hv : s • v ∈ B) : t • v ∈ B := by
  obtain ⟨c, rfl⟩ := h
  rw [mul_comm, mul_smul]
  exact B.smul_mem c hv

end Ideals

section Unimod

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem hermE_one (x y : Fin n → E) :
    hermE (IsCMField.complexConj E) 1 x y = ∑ j, IsCMField.complexConj E (y j) * x j := by
  simp [hermE, Matrix.one_apply, mul_comm]

theorem unimod_move (γ : GL (Fin n) E) (hγ : IsUnE (IsCMField.complexConj E) 1 γ.1) (Λ Λ' : GenLat E n)
    (h : ∀ v, v ∈ Λ.La ↔ γ.1 *ᵥ v ∈ Λ'.La) (hU : Λ.Unimod) : Λ'.Unimod := by
  have hs : ∀ v : Fin n → E, ∃ u, v = γ.1 *ᵥ u := fun v =>
    ⟨(γ⁻¹).1 *ᵥ v, by rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
  intro v
  obtain ⟨u, rfl⟩ := hs v
  rw [← h, hU u]
  constructor
  · intro H w hw
    obtain ⟨x, rfl⟩ := hs w
    rw [← hermE_one, hγ, hermE_one]
    exact H x ((h x).2 hw)
  · intro H x hx
    have := H _ ((h x).1 hx)
    rwa [← hermE_one, hγ, hermE_one] at this

end Unimod

end GlobalTheory.UnRep.Move
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory.AdeleCM

theorem exists_adele_tensor_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) → letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E); ∃ Φ : AdeleRing (𝓞 F) F ⊗[F] E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (1 ⊗ₜ[F] x) = (mixedEmbedding E x, algebraMap E _ x)) ∧ (∀ y, Algebra.TensorProduct.map (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (AlgHom.id F E) y ∈ AddSubgroup.closure {y : FiniteAdeleRing (𝓞 F) F ⊗[F] E | ∃ a ∈ {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (ε : AdeleRing (𝓞 F) F), ε.1 = 0 → ε.2 v = 1 → (∀ v', v' ≠ v → ε.2 v' = 0) → (Φ (ε ⊗ₜ[F] 1)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (ε ⊗ₜ[F] 1)).2 P = if P.under (𝓞 F) = v then 1 else 0) ∧ Continuous Φ.symm ∧ ∀ x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)ˣ, (x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).2 = 1 → (∀ w, ((x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).1.2 w).im = 0) → ∃ a : (AdeleRing (𝓞 F) F)ˣ, Φ ((a : AdeleRing (𝓞 F) F) ⊗ₜ[F] 1) = x := by
  intro F E _ _ _ _ _ σ hF hE h2 hσ
  letI t1 : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E)
  letI t2 : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
  letI t3 : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  obtain ⟨e, he, -, hec⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  obtain ⟨ι, hι1, hι2, hι3⟩ := GlobalTheory.AdeleBaseChange.exists_tensor_finiteAdele_equiv F E
  have hιc := GlobalTheory.AdeleBaseChange.continuous_symm_finite F E ι hι2
  obtain ⟨θ, hθ1, hθc, hθ3⟩ := GlobalTheory.T.exists_infiniteAdele_tensor_equiv_mixedSpace F E σ hF hE h2 hσ
  have he1 : ∀ (a : AdeleRing (𝓞 F) F) (x : E), (e (a ⊗ₜ[F] x)).1 = a.1 ⊗ₜ[F] x :=
    fun a x => (he _).1.trans (Algebra.TensorProduct.map_tmul _ _ _ _)
  have he2 : ∀ (a : AdeleRing (𝓞 F) F) (x : E), (e (a ⊗ₜ[F] x)).2 = a.2 ⊗ₜ[F] x :=
    fun a x => (he _).2.trans (Algebra.TensorProduct.map_tmul _ _ _ _)
  let Φ : AdeleRing (𝓞 F) F ⊗[F] E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E) :=
    e.trans (RingEquiv.prodCongr θ ι)
  have hΦ : ∀ z, Φ z = (θ (e z).1, ι (e z).2) := fun z => rfl
  refine ⟨Φ, fun x => ?_, fun y => ?_, fun v ε h0 h1 hv => ⟨?_, fun P => ?_⟩, ?_, fun x hx2 hx1 => ?_⟩
  · rw [hΦ, he1, he2]
    exact Prod.ext (hθ1 x) (hι1 x)
  · rw [← (he y).2]
    exact hι2 (e y).2
  · rw [hΦ, he1, h0]
    simp
  · rw [hΦ, he2]
    exact hι3 v ε.2 h1 hv P
  · have : (Φ.symm : _ → _) = fun w => e.symm (θ.symm w.1, ι.symm w.2) := rfl
    rw [this]
    exact hec.comp ((hθc.comp continuous_fst).prodMk (hιc.comp continuous_snd))
  · obtain ⟨a, ha⟩ := hθ3 (Units.map (RingHom.fst (mixedSpace E) (FiniteAdeleRing (𝓞 E) E)).toMonoidHom x) hx1
    refine ⟨⟨((a : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)),
      ((a⁻¹ : (InfiniteAdeleRing F)ˣ), (1 : FiniteAdeleRing (𝓞 F) F)), ?_, ?_⟩, ?_⟩
    · exact Prod.ext a.mul_inv (mul_one _)
    · exact Prod.ext a.inv_mul (mul_one _)
    · rw [hΦ, he1, he2]
      refine Prod.ext ha ?_
      rw [hx2]
      exact map_one ι

end GlobalTheory.AdeleCM
end
