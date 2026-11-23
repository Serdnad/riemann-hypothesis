module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem charpoly_mulLeft_eq_of_gen {F A : Type} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (u : A) (Q : F[X]) (hQ : Q.Monic) (hadj : Algebra.adjoin F {u} = ⊤) (hr : aeval u Q = 0)
    (hd : Module.finrank F A = Q.natDegree) : (LinearMap.mulLeft F u).charpoly = Q := by
  set P := (LinearMap.mulLeft F u).charpoly with hPdef
  have hP : P.Monic := LinearMap.charpoly_monic _
  have hPd : P.natDegree = Q.natDegree := by rw [hPdef, LinearMap.charpoly_natDegree, hd]
  by_cases hQ1 : Q = 1
  · subst hQ1
    rw [natDegree_one] at hPd
    exact Polynomial.eq_one_of_monic_natDegree_zero hP hPd
  set d := Q.natDegree with hddef
  let v : Fin d → A := fun i => u ^ (i : ℕ)
  have hsp : ⊤ ≤ Submodule.span F (Set.range v) := by
    intro a _
    have ha : a ∈ Algebra.adjoin F {u} := hadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨p, rfl⟩ := ha
    show aeval u p ∈ _
    rw [← Polynomial.aeval_modByMonic_eq_self_of_root hr,
      Polynomial.aeval_eq_sum_range' (Polynomial.natDegree_modByMonic_lt p hQ hQ1)]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, Finset.mem_range.1 hi⟩, rfl⟩)
  have hli : LinearIndependent F v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hsp (by simp [hd, hddef])
  have hPu : aeval u P = 0 := by
    have h1 := LinearMap.aeval_self_charpoly (LinearMap.mulLeft F u)
    have h2 : (Algebra.lmul F A) u = LinearMap.mulLeft F u := by ext; simp
    rw [← hPdef, ← h2, Polynomial.aeval_algHom_apply] at h1
    have h3 := congrArg (fun f : Module.End F A => f 1) h1
    simpa using h3
  by_contra hne
  have hR : P - Q ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (P - Q).degree < d := by
    have := Polynomial.degree_sub_lt (p := P) (q := Q) (by rw [Polynomial.degree_eq_natDegree hP.ne_zero,
      Polynomial.degree_eq_natDegree hQ.ne_zero, hPd]) hP.ne_zero (by rw [hP.leadingCoeff, hQ.leadingCoeff])
    rwa [Polynomial.degree_eq_natDegree hP.ne_zero, hPd] at this
  have hRd : (P - Q).natDegree < d := (Polynomial.natDegree_lt_iff_degree_lt hR).2 hdeg
  have hz : aeval u (P - Q) = 0 := by simp [hPu, hr]
  rw [Polynomial.aeval_eq_sum_range' hRd, Finset.sum_range (fun i => (P - Q).coeff i • u ^ i)] at hz
  have hc := (Fintype.linearIndependent_iff.1 hli) (fun i => (P - Q).coeff i) hz ⟨_, hRd⟩
  exact hR (Polynomial.leadingCoeff_eq_zero.1 hc)

theorem charpoly_of_semilinear {F L A : Type} [Field F] [Field L] [CommRing A] [Algebra F A] [Module.Finite F A]
    (e : F ≃+* L) {n : ℕ} (u : A) (g : Matrix (Fin n) (Fin n) L) (ψ : A ≃+ (Fin n → L))
    (hψ : ∀ (c : F) (y : A), ψ (c • y) = e c • ψ y) (hu : ∀ y, ψ (u * y) = g *ᵥ ψ y) :
    g.charpoly = (LinearMap.mulLeft F u).charpoly.map (e : F →+* L) := by
  let b := Module.finBasis F A
  set d := Module.finrank F A
  let v : Fin d → (Fin n → L) := fun i => ψ (b i)
  have hsum : ∀ c : Fin d → L, ∑ i, c i • v i = ψ (∑ i, e.symm (c i) • b i) := by
    intro c

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hψ, e.apply_symm_apply]
  have hli : LinearIndependent L v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    rw [hsum, map_eq_zero_iff ψ ψ.injective] at hc
    have := (Fintype.linearIndependent_iff.1 b.linearIndependent) _ hc i
    simpa using this
  have hsp : ⊤ ≤ Submodule.span L (Set.range v) := by
    intro x _
    obtain ⟨a, rfl⟩ := ψ.surjective x

    rw [← b.sum_repr a, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hψ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' : Module.Basis (Fin d) L (Fin n → L) := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = v i := fun i => Module.Basis.mk_apply hli hsp i
  let M := LinearMap.toMatrix b b (LinearMap.mulLeft F u)
  have key : LinearMap.toMatrix b' b' (Matrix.toLin' g) = M.map (e : F →+* L) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, hb', Matrix.toLin'_apply]
    have h1 : g *ᵥ v j = ∑ k, e (b.repr (u * b j) k) • b' k := by
      show g *ᵥ ψ (b j) = _
      rw [← hu]
      conv_lhs => rw [← b.sum_repr (u * b j)]

      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hψ, hb']
    rw [h1, b'.repr_sum_self]
    simp [M, LinearMap.toMatrix_apply, Algebra.leftMulMatrix_eq_repr_mul]
  calc g.charpoly = (Matrix.toLin' g).charpoly := by
        rw [← LinearMap.charpoly_toMatrix (Matrix.toLin' g) (Pi.basisFun L (Fin n)),
          LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    _ = (M.map (e : F →+* L)).charpoly := by rw [← key, LinearMap.charpoly_toMatrix]
    _ = _ := by rw [Matrix.charpoly_map, LinearMap.charpoly_toMatrix]

theorem charpoly_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E) (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K)
    (u x : B.A) (γ : GLw n w), Q.Monic → Fits w e B Q u → IsModel w e B u x γ → γ.val.charpoly = Q := by
  intro E _ _ _ w K e n Q B u x γ hQ hfit hmod
  obtain ⟨hadj, hr, hd, -⟩ := hfit
  obtain ⟨ψ, hψ, hu, -⟩ := hmod
  rw [charpoly_of_semilinear e u γ.val ψ hψ hu,
    charpoly_mulLeft_eq_of_gen u (Q.map e.symm.toRingHom) (hQ.map _) hadj hr (by rw [hd, natDegree_map]),
    Polynomial.map_map]
  ext i
  simp [Polynomial.coeff_map]

end GlobalTheory.KapLat
end
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem fits_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K)
    (u₁ : B₁.A) (u₂ : B₂.A), (Q₁ * Q₂).Separable → Fits w e B₁ Q₁ u₁ → Fits w e B₂ Q₂ u₂ →
    Fits w e (B₁.prod B₂) (Q₁ * Q₂) ((u₁, u₂) : B₁.A × B₂.A) := by
  intro E _ _ _ w K e Q₁ Q₂ B₁ B₂ u₁ u₂ hsep h₁ h₂
  obtain ⟨ha₁, hr₁, hd₁, hs₁⟩ := h₁
  obtain ⟨ha₂, hr₂, hd₂, hs₂⟩ := h₂
  have hne : Q₁ * Q₂ ≠ 0 := hsep.ne_zero
  have hQ₁ : Q₁ ≠ 0 := left_ne_zero_of_mul hne
  have hQ₂ : Q₂ ≠ 0 := right_ne_zero_of_mul hne
  have hcop : IsCoprime (Q₁.map e.symm.toRingHom) (Q₂.map e.symm.toRingHom) :=
    hsep.isCoprime.map (Polynomial.mapRingHom e.symm.toRingHom)
  have hfst : ∀ p : K.E[X], (aeval ((u₁, u₂) : B₁.A × B₂.A) p).1 = aeval u₁ p := fun p => by
    simpa using (Polynomial.aeval_algHom_apply (AlgHom.fst K.E B₁.A B₂.A) ((u₁, u₂) : B₁.A × B₂.A) p).symm
  have hsnd : ∀ p : K.E[X], (aeval ((u₁, u₂) : B₁.A × B₂.A) p).2 = aeval u₂ p := fun p => by
    simpa using (Polynomial.aeval_algHom_apply (AlgHom.snd K.E B₁.A B₂.A) ((u₁, u₂) : B₁.A × B₂.A) p).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Algebra.adjoin K.E {((u₁, u₂) : B₁.A × B₂.A)} = ⊤
    obtain ⟨a, b, hab⟩ := hcop
    have e₁ : aeval u₁ b * aeval u₁ (Q₂.map e.symm.toRingHom) = 1 := by
      have := congrArg (aeval u₁) hab
      rw [map_add (f := _), map_mul, map_mul, hr₁, mul_zero, zero_add, map_one] at this
      exact this
    have e₂ : aeval u₂ a * aeval u₂ (Q₁.map e.symm.toRingHom) = 1 := by
      have := congrArg (aeval u₂) hab
      rw [map_add (f := _), map_mul, map_mul, hr₂, mul_zero, add_zero, map_one] at this
      exact this
    rw [eq_top_iff]
    rintro ⟨y, z⟩ -
    have hy : y ∈ (aeval u₁ : K.E[X] →ₐ[K.E] B₁.A).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, ha₁]; trivial
    have hz : z ∈ (aeval u₂ : K.E[X] →ₐ[K.E] B₂.A).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, ha₂]; trivial
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨r, rfl⟩ := hz
    have key : ((aeval u₁ p, aeval u₂ r) : B₁.A × B₂.A) =
        aeval ((u₁, u₂) : B₁.A × B₂.A) (b * Q₂.map e.symm.toRingHom * p + a * Q₁.map e.symm.toRingHom * r) := by
      refine Prod.ext ?_ ?_
      · rw [hfst, map_add (f := _), map_mul, map_mul, map_mul, map_mul, hr₁, mul_zero, zero_mul, add_zero, e₁, one_mul]
      · rw [hsnd, map_add (f := _), map_mul, map_mul, map_mul, map_mul, hr₂, mul_zero, zero_mul, zero_add, e₂, one_mul]
    exact key ▸ Polynomial.aeval_mem_adjoin_singleton K.E _
  · show aeval ((u₁, u₂) : B₁.A × B₂.A) ((Q₁ * Q₂).map e.symm.toRingHom) = 0
    rw [Polynomial.map_mul]
    refine Prod.ext ?_ ?_
    · rw [hfst, map_mul, hr₁, zero_mul]; rfl
    · rw [hsnd, map_mul, hr₂, mul_zero]; rfl
  · show Module.finrank K.E (B₁.A × B₂.A) = (Q₁ * Q₂).natDegree
    rw [Module.finrank_prod, hd₁, hd₂, natDegree_mul hQ₁ hQ₂]
  · exact Prod.ext hs₁ hs₂

end GlobalTheory.KapLat
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem models_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ γ' : GLw n w), IsModel w e B u x γ → IsModel w e B u x γ' → ∃ y ∈ UL n w, γ' = y⁻¹ * γ * y := by
  intro E _ _ _ w hw K e B u x n γ γ' hγ hγ'
  obtain ⟨ψ, hψl, hψu, hψh⟩ := hγ
  obtain ⟨ψ', hψ'l, hψ'u, hψ'h⟩ := hγ'
  let f : (Fin n → w.adicCompletion E) →ₗ[w.adicCompletion E] (Fin n → w.adicCompletion E) :=
    { toFun := fun v => ψ (ψ'.symm v)
      map_add' := by intro a b; simp
      map_smul' := by
        intro t v
        obtain ⟨c, rfl⟩ : ∃ c, e c = t := ⟨e.symm t, e.apply_symm_apply t⟩
        obtain ⟨a, rfl⟩ : ∃ a, ψ' a = v := ⟨ψ'.symm v, ψ'.apply_symm_apply v⟩
        simp only [RingHom.id_apply]
        rw [← hψ'l, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, hψl] }
  let g : (Fin n → w.adicCompletion E) →ₗ[w.adicCompletion E] (Fin n → w.adicCompletion E) :=
    { toFun := fun v => ψ' (ψ.symm v)
      map_add' := by intro a b; simp
      map_smul' := by
        intro t v
        obtain ⟨c, rfl⟩ : ∃ c, e c = t := ⟨e.symm t, e.apply_symm_apply t⟩
        obtain ⟨a, rfl⟩ : ∃ a, ψ a = v := ⟨ψ.symm v, ψ.apply_symm_apply v⟩
        simp only [RingHom.id_apply]
        rw [← hψl, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, hψ'l] }
  have hfg : f ∘ₗ g = LinearMap.id := LinearMap.ext fun v => by simp [f, g]
  have hgf : g ∘ₗ f = LinearMap.id := LinearMap.ext fun v => by simp [f, g]
  let y : GLw n w := ⟨LinearMap.toMatrix' f, LinearMap.toMatrix' g,
    by rw [← LinearMap.toMatrix'_comp, hfg, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_comp, hgf, LinearMap.toMatrix'_id]⟩
  have hy : ∀ v, (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) *ᵥ v = f v := fun v =>
    LinearMap.toMatrix'_mulVec f v

  have hinv : ∀ v v', stdH w (f v) (f v') = stdH w v v' := by
    intro v v'
    obtain ⟨a, rfl⟩ : ∃ a, ψ' a = v := ⟨ψ'.symm v, ψ'.apply_symm_apply v⟩
    obtain ⟨b, rfl⟩ : ∃ b, ψ' b = v' := ⟨ψ'.symm v', ψ'.apply_symm_apply v'⟩
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply]
    rw [hψh, hψ'h]
  refine ⟨y, ?_, ?_⟩
  · unfold UL
    rw [if_neg hw]
    change Formalism.UG.cT (cj w) (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 *
      (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = 1
    set M : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hM
    have key : Mᵀ * M.map (cj w) = 1 := by
      refine Matrix.ext fun i j => ?_
      have h1 := hinv (Pi.single i 1) (Pi.single j 1)
      rw [← hy, ← hy] at h1
      simp only [stdH, Matrix.mulVec_single_one] at h1
      have h2 : (if i = j then (1 : w.adicCompletion E) else 0) = ∑ k, M k i * cj w (M k j) := by
        simpa [Pi.single_apply, eq_comm] using h1
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [Matrix.transpose_apply, Matrix.map_apply]
      exact h2.symm
    have key2 := congrArg Matrix.transpose key
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at key2
    rw [Matrix.mul_one]
    exact key2
  ·
    have hc : (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * γ'.val = γ.val * y := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      obtain ⟨a, rfl⟩ : ∃ a, ψ' a = v := ⟨ψ'.symm v, ψ'.apply_symm_apply v⟩
      simp only [Matrix.toLin'_apply]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hψ'u, hy, hy]
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply]
      rw [hψu]
    have hc' : y * γ' = γ * y := Units.ext hc
    rw [mul_assoc, ← hc', ← mul_assoc, inv_mul_cancel, one_mul]

end GlobalTheory.KapLat
end

section

noncomputable section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapOrb

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsModelMap (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K)
    (u x : B.A) {n : ℕ} (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) : Prop :=
  (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) ∧ (∀ y, ψ (u * y) = γ.val *ᵥ ψ y) ∧
    ∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z)

theorem isModel_iff (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K)
    (u x : B.A) {n : ℕ} (γ : GLw n w) : IsModel w e B u x γ ↔ ∃ ψ, IsModelMap w e B u x γ ψ := Iff.rfl

def pullLat (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g : GLw n w) : Submodule K.O B.A where
  carrier := {y | ∀ (c : K.O) (i : Fin n), ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E}
  zero_mem' := by
    intro c i
    simp
  add_mem' := by
    intro a b ha hb c i
    rw [smul_add, map_add (f := _), Matrix.mulVec_add, Pi.add_apply]
    exact add_mem (ha c i) (hb c i)
  smul_mem' := by
    intro c' a ha c i
    rw [smul_smul]
    exact ha (c * c') i

def torusOf (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g : GLw n w) : B.Aˣ :=
  if h : ∃ a : B.Aˣ, ∀ y, ψ ((a : B.A) * y) = g.val *ᵥ ψ y then h.choose else 1

theorem torusOf_spec (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g : GLw n w) (a : B.Aˣ)
    (ha : ∀ y, ψ ((a : B.A) * y) = g.val *ᵥ ψ y) : torusOf w B ψ g = a := by
  have h : ∃ a : B.Aˣ, ∀ y, ψ ((a : B.A) * y) = g.val *ᵥ ψ y := ⟨a, ha⟩
  unfold torusOf
  rw [dite_eq_left h]
  apply Units.ext
  have h1 := h.choose_spec 1
  have h2 := ha 1
  rw [mul_one] at h1 h2
  exact ψ.injective (h1.trans h2.symm)

end GlobalTheory.KapOrb
end
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

noncomputable section

namespace GlobalTheory.KapLat.ModelOfBasis

variable {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K)

theorem herm_sum_left (x z : B.A) {ι : Type} (s : Finset ι) (f : ι → B.A) :
    B.herm x (∑ k ∈ s, f k) z = ∑ k ∈ s, B.herm x (f k) z := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm

  rw [Finset.mul_sum, Finset.sum_mul, map_sum]

theorem herm_sum_right (x y : B.A) {ι : Type} (s : Finset ι) (f : ι → B.A) :
    B.herm x y (∑ k ∈ s, f k) = ∑ k ∈ s, B.herm x y (f k) := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm

  rw [map_sum, Finset.mul_sum, map_sum]

theorem herm_eq_sum {n : ℕ} (x : B.A) (b : Module.Basis (Fin n) K.E B.A)
    (hb : ∀ i j, B.herm x (b i) (b j) = if i = j then 1 else 0) (y z : B.A) :
    B.herm x y z = ∑ k, b.repr y k * K.c (b.repr z k) := by
  conv_lhs => rw [← b.sum_repr y, ← b.sum_repr z]
  rw [herm_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [herm_sum_right, Finset.sum_eq_single k]
  · rw [GlobalTheory.UnitLemma.Basic.herm_smul_left, GlobalTheory.UnitLemma.Basic.herm_smul_right, hb, if_pos rfl]; ring
  · intro l _ hl
    rw [GlobalTheory.UnitLemma.Basic.herm_smul_left, GlobalTheory.UnitLemma.Basic.herm_smul_right, hb, if_neg (Ne.symm hl)]; ring
  · intro h; exact absurd (Finset.mem_univ k) h

end GlobalTheory.KapLat.ModelOfBasis

open GlobalTheory.KapLat.ModelOfBasis in
theorem GlobalTheory.KapLat.exists_model_of_orthonormal_basis :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e →
    ∀ (n : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), u * B.σ u = 1 →
    ∀ b : Module.Basis (Fin n) K.E B.A, (∀ i j, B.herm x (b i) (b j) = if i = j then 1 else 0) →
    ∃ γ : GLw n w, γ ∈ UL n w ∧ IsModel w e B u x γ := by
  intro E _ _ _ w hw K e hbr n B u x hu b hb
  let ψ : B.A ≃+ (Fin n → w.adicCompletion E) :=
    b.equivFun.toAddEquiv.trans (AddEquiv.piCongrRight fun _ => e.toAddEquiv)
  have hψ : ∀ y k, ψ y k = e (b.repr y k) := fun y k => rfl
  have hstd : ∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z) := by
    intro y z

    rw [herm_eq_sum B x b hb, map_sum]
    unfold stdH
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hψ, hψ, map_mul, hbr.1]
  let M : Matrix (Fin n) (Fin n) (w.adicCompletion E) := Matrix.of fun k i => e (b.repr (u * b i) k)
  have hM : ∀ y, ψ (u * y) = M *ᵥ ψ y := by
    intro y
    funext k
    have hy : u * y = ∑ i, b.repr y i • (u * b i) := by
      conv_lhs => rw [← b.sum_repr y]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _

    rw [hψ, hy, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_sum]
    simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, hψ, map_smul, Finsupp.smul_apply, smul_eq_mul,
      map_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hunit : cT (cj w) M * M = 1 := by
    ext i j
    have h := hstd (u * b j) (u * b i)
    rw [← GlobalTheory.UnitLemma.Basic.herm_norm, hu, mul_one, hb] at h
    simp only [stdH, hψ] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, M, Matrix.of_apply]
    rw [Finset.sum_congr rfl fun k _ => mul_comm _ _, h]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg (Ne.symm hij), if_neg hij, map_zero]
  have hunit' : M * cT (cj w) M = 1 := mul_eq_one_comm.mp hunit
  let γ : GLw n w := ⟨M, cT (cj w) M, hunit', hunit⟩
  refine ⟨γ, ?_, ψ, ?_, hM, hstd⟩
  · unfold UL
    rw [if_neg hw]
    show cT (cj w) M * 1 * M = 1
    rw [Matrix.mul_one, hunit]
  · intro c y
    funext k
    rw [hψ, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply, hψ, smul_eq_mul]
end
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.TwLatMul

theorem col_eq {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
    (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ}
    (b : Module.Basis (Fin m) K.E B.A) (a : B.A) (g h : GLw m w)
    (hh : h.val = GlobalTheory.TwLat.mulMat e b a * g.val) (j : Fin m) :
    ∑ i, e.symm (h.val i j) • b i = a * ∑ i, e.symm (g.val i j) • b i := by
  set M := LinearMap.toMatrix b b (LinearMap.mulLeft K.E a) with hM
  have hij : ∀ i, e.symm (h.val i j) = ∑ k, M i k * e.symm (g.val k j) := by
    intro i
    rw [hh]

    simp [Matrix.mul_apply, GlobalTheory.TwLat.mulMat, map_sum, map_mul, hM]
  have hab : ∀ k, a * b k = ∑ i, M i k • b i := by
    intro k
    simp only [hM, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply]
    exact (b.sum_repr _).symm
  simp_rw [hij, Finset.mul_sum, mul_smul_comm, hab, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp_rw [mul_comm]

theorem lat_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (a : B.A) (g h : GLw m w), h.val = GlobalTheory.TwLat.mulMat e b a * g.val → GlobalTheory.TwLat.lat e b h = GlobalTheory.UnitLemma.mulLat K.O a (GlobalTheory.TwLat.lat e b g) := by
  intro E _ _ _ _ w _ K e _ _ _ B m b a g h hh
  unfold GlobalTheory.TwLat.lat GlobalTheory.UnitLemma.mulLat
  rw [Submodule.map_span, ← Set.range_comp]
  refine congrArg _ (congrArg Set.range (funext fun j => ?_))
  exact col_eq e b a g h hh j

end GlobalTheory.TwLatMul
end

end

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

theorem _root_.GlobalTheory.T.charpoly_eq_of_hermitianMultiplicationModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (γ : GLw n w), Q.Monic → Fits w e B Q u → IsModel w e B u x γ → γ.val.charpoly = Q := by
  first | exact @GlobalTheory.KapLat.charpoly_of_model | exact GlobalTheory.KapLat.charpoly_of_model | (intros; apply GlobalTheory.KapLat.charpoly_of_model <;> assumption)

end
end

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

theorem _root_.GlobalTheory.T.conj_unitary_of_same_hermitianMultiplicationModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ γ' : GLw n w), IsModel w e B u x γ → IsModel w e B u x γ' → ∃ y ∈ UL n w, γ' = y⁻¹ * γ * y := by
  first | exact @GlobalTheory.KapLat.models_conj | exact GlobalTheory.KapLat.models_conj | (intros; apply GlobalTheory.KapLat.models_conj <;> assumption)

end
end

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

theorem _root_.GlobalTheory.T.exists_hermitianModel_of_orthonormal_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e →
    ∀ (n : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), u * B.σ u = 1 →
    ∀ b : Module.Basis (Fin n) K.E B.A, (∀ i j, B.herm x (b i) (b j) = if i = j then 1 else 0) →
    ∃ γ : GLw n w, γ ∈ UL n w ∧ IsModel w e B u x γ := by
  first | exact @GlobalTheory.KapLat.exists_model_of_orthonormal_basis | exact GlobalTheory.KapLat.exists_model_of_orthonormal_basis | (intros; apply GlobalTheory.KapLat.exists_model_of_orthonormal_basis <;> assumption)

end
end

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

theorem _root_.GlobalTheory.T.prod_adjoinRootAlgebras_generated_by_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K) (u₁ : B₁.A) (u₂ : B₂.A), (Q₁ * Q₂).Separable → Fits w e B₁ Q₁ u₁ → Fits w e B₂ Q₂ u₂ → Fits w e (B₁.prod B₂) (Q₁ * Q₂) ((u₁, u₂) : B₁.A × B₂.A) := by
  first | exact @GlobalTheory.KapLat.fits_prod | exact GlobalTheory.KapLat.fits_prod | (intros; apply GlobalTheory.KapLat.fits_prod <;> assumption)

end
end

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.latticeSpannedByGLColumns_mulLeftMatrix_eq_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (a : B.A) (g h : GLw m w), h.val = GlobalTheory.TwLat.mulMat e b a * g.val → GlobalTheory.TwLat.lat e b h = GlobalTheory.UnitLemma.mulLat K.O a (GlobalTheory.TwLat.lat e b g) := by
  first | exact @GlobalTheory.TwLatMul.lat_mul | exact GlobalTheory.TwLatMul.lat_mul | (intros; apply GlobalTheory.TwLatMul.lat_mul <;> assumption)

end
end
