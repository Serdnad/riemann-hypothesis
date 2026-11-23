module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix NumberField NumberField.ComplexEmbedding

noncomputable section

namespace DualLineConjugation

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T] [DecidableEq T]

def conjPerm (K : Type) [Field K] : Equiv.Perm (K →+* ℂ) :=
  Function.Involutive.toPerm _ (involutive_conjugate K)


omit [Fintype T] [DecidableEq T] in
theorem conj_mulVec (b : Module.Basis T ℤ (dualLattice F)) (w : (K →+* ℂ) × Fin i → ℂ) :
    (fun t => starRingEnd ℂ ((dualEmbMatrix b *ᵥ w) t)) =
      dualEmbMatrix b *ᵥ fun p => starRingEnd ℂ (w (conjugate p.1, p.2)) := by
  funext t

  simp only [mulVec, dotProduct, map_sum, map_mul]
  refine Fintype.sum_equiv ((conjPerm K).prodCongr (Equiv.refl _)) _ _ fun p => ?_
  simp [conjPerm, dualEmbMatrix]

theorem recover_conj (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : T → ℂ) :
    dualRecover b hb (fun t => starRingEnd ℂ (z t)) =
      fun p => starRingEnd ℂ (dualRecover b hb z (conjugate p.1, p.2)) := by
  have h1 : ∀ w, (dualRecover b hb).symm w = dualEmbMatrix b *ᵥ w := fun w => by
    simp [dualRecover]
  apply (dualRecover b hb).symm.injective
  rw [LinearEquiv.symm_apply_apply, h1, ← conj_mulVec b (dualRecover b hb z), ← h1,
    LinearEquiv.symm_apply_apply]

theorem re_conj_form {n : Type} [Fintype n] (H : Matrix n n ℂ) (v : n → ℂ) :
    (star (fun j => starRingEnd ℂ (v j)) ⬝ᵥ (H *ᵥ fun j => starRingEnd ℂ (v j))).re =
      (star v ⬝ᵥ (H.map (starRingEnd ℂ) *ᵥ v)).re := by
  rw [← Complex.conj_re (star v ⬝ᵥ _)]
  congr 1

  simp [dotProduct, mulVec, map_sum, map_mul]

theorem normSq_conj (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : T → ℂ) :
    dualNormSq b hb (fun t => starRingEnd ℂ (z t)) = dualNormSq b hb z := by
  unfold dualNormSq
  rw [recover_conj]
  refine Fintype.sum_equiv (conjPerm K) _ _ fun σ => ?_
  have hσ : conjPerm K σ = conjugate σ := rfl
  rw [hσ, F.conj σ]
  exact re_conj_form (F.metric σ) fun j => dualRecover b hb z (conjugate σ, j)

end DualLineConjugation

theorem DualLineConj.proof : DualLineConj.Statement := by
  intro K _ _ i F T _ _ b hb z
  show Real.sqrt (dualNormSq b hb fun t => starRingEnd ℂ (z ⟨(), t⟩)) =
    Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩)
  rw [DualLineConjugation.normSq_conj b hb fun t => z ⟨(), t⟩]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix

noncomputable section

namespace DualEmbeddingBijective

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem exists_zsmul_mem_dualLattice (F : HermLattice K i) (y : Fin i → K) :
    ∃ N : ℤ, N ≠ 0 ∧ N • y ∈ dualLattice F := by
  classical
  obtain ⟨S, hS⟩ := F.fg
  obtain ⟨d, hd0, hd⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image y ∪ S.biUnion fun g => Finset.univ.image g)
  have hint : ∀ z : K, IsIntegral ℤ z → z ∈ (algebraMap (𝓞 K) K).range :=
    fun z hz => ⟨⟨z, hz⟩, rfl⟩
  refine ⟨d * d, mul_ne_zero hd0 hd0, ?_⟩
  intro x hx
  rw [← hS] at hx
  refine Submodule.span_induction
    (p := fun x _ => ((d * d) • y) ⬝ᵥ x ∈ (algebraMap (𝓞 K) K).range) ?_ ?_ ?_ ?_ hx
  · intro g hg
    have hsum : ((d * d) • y) ⬝ᵥ g = ∑ j, (d • y j) * (d • g j) := by
      simp only [dotProduct, Pi.smul_apply, zsmul_eq_mul, Int.cast_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsum]
    refine sum_mem fun j _ => mul_mem (hint _ (hd _ ?_)) (hint _ (hd _ ?_))
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨g, Finset.mem_coe.mp hg, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩)
  · rw [dotProduct_zero]
    exact zero_mem _
  · intro x z _ _ hx hz
    rw [dotProduct_add]
    exact add_mem hx hz
  · intro a x _ hx
    obtain ⟨c, hc⟩ := hx
    exact ⟨a * c, by rw [dotProduct_smul, map_mul, hc]; rfl⟩

def pairing (w : (K →+* ℂ) × Fin i → ℂ) : (Fin i → K) →+ ℂ where
  toFun φ := ∑ p, p.1 (φ p.2) * w p
  map_zero' := by simp
  map_add' φ ψ := by simp [add_mul, Finset.sum_add_distrib]

theorem pairing_single (w : (K →+* ℂ) × Fin i → ℂ) (j : Fin i) (x : K) :
    pairing w (Pi.single j x) = ∑ σ : K →+* ℂ, w (σ, j) * σ x := by
  classical
  simp only [pairing, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro j' _ hj'
    simp [Pi.single_eq_of_ne hj']
  · simp

theorem injective (F : HermLattice K i) {T : Type} [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice F)) :
    Function.Injective (Matrix.mulVecLin (dualEmbMatrix b)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  have hb : ∀ t, pairing w (b t : Fin i → K) = 0 := fun t => by
    have h := congrFun hw t
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, dualEmbMatrix, pairing] using h
  have hL : ∀ φ : dualLattice F, pairing w φ = 0 := by
    intro φ

    rw [← b.sum_repr φ, Submodule.coe_sum, map_sum]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [Submodule.coe_smul, map_zsmul, hb, smul_zero]
  have hK : ∀ y, pairing w y = 0 := by
    intro y
    obtain ⟨N, hN, hy⟩ := exists_zsmul_mem_dualLattice F y
    have h := hL ⟨_, hy⟩
    rw [Submodule.coe_mk, map_zsmul] at h
    exact (smul_eq_zero.mp h).resolve_left hN
  funext p
  obtain ⟨σ, j⟩ := p
  have hli := (linearIndependent_monoidHom K ℂ).comp (fun σ : K →+* ℂ => σ.toMonoidHom)
    (fun σ τ h => RingHom.ext fun x => DFunLike.congr_fun h x)
  rw [Fintype.linearIndependent_iff] at hli
  refine hli (fun σ => w (σ, j)) ?_ σ
  funext x
  have h := hK (Pi.single j x)
  rw [pairing_single] at h
  simpa [Finset.sum_apply] using h

theorem card_le (F : HermLattice K i) {T : Type} [Fintype T]
    (b : Module.Basis T ℤ (dualLattice F)) :
    Fintype.card T ≤ Fintype.card ((K →+* ℂ) × Fin i) := by
  have h1 : LinearIndependent ℤ (fun t => (b t : Fin i → K)) :=
    b.linearIndependent.map' (dualLattice F).subtype (Submodule.ker_subtype _)
  have h2 : LinearIndependent ℚ (fun t => (b t : Fin i → K)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp h1
  have h3 := h2.fintype_card_le_finrank
  rw [Module.finrank_pi_fintype] at h3
  rw [Fintype.card_prod, NumberField.Embeddings.card K ℂ, Fintype.card_fin]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h3
  rw [mul_comm]
  exact h3

end DualEmbeddingBijective

theorem DualEmbBijective.proof : DualEmbBijective.Statement := by
  intro K _ _ i F T _ _ b
  have hinj := DualEmbeddingBijective.injective F b
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hcard := DualEmbeddingBijective.card_le F b
  simp only [Module.finrank_fintype_fun_eq_card] at hle
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
  simp only [Module.finrank_fintype_fun_eq_card]
  omega

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix NumberField

noncomputable section

namespace DualLatticeBasisExistsAlt

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem eq_zero_of_dotProduct_gens (F : HermLattice K i) (s : Finset (Fin i → K))
    (hs : Submodule.span (𝓞 K) (s : Set (Fin i → K)) = F.lattice) (φ : Fin i → K)
    (h : ∀ g ∈ s, φ ⬝ᵥ g = 0) : φ = 0 := by
  let L : (Fin i → K) →ₗ[K] K :=
    { toFun := fun x => φ ⬝ᵥ x
      map_add' := dotProduct_add φ
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have h1 : F.lattice ≤ (LinearMap.ker L).restrictScalars (𝓞 K) := by
    rw [← hs, Submodule.span_le]
    intro g hg
    exact h g hg
  have h2 : Submodule.span K (F.lattice : Set (Fin i → K)) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    intro x hx
    exact h1 hx
  rw [F.span_eq, top_le_iff] at h2
  funext j
  have hj : Pi.single j (1 : K) ∈ LinearMap.ker L := by rw [h2]; trivial
  have : φ ⬝ᵥ Pi.single j (1 : K) = 0 := hj
  simpa [dotProduct_single] using this

theorem dualLattice_fg (F : HermLattice K i) : (dualLattice F).FG := by
  classical
  obtain ⟨s, hs⟩ := F.fg

  let G : (Fin i → K) →ₗ[ℤ] (s → K) :=
    { toFun := fun φ g => φ ⬝ᵥ (g : Fin i → K)
      map_add' := fun φ ψ => by funext g; simp [add_dotProduct]
      map_smul' := fun c φ => by
        funext g
        show (c • φ) ⬝ᵥ (g : Fin i → K) = c • (φ ⬝ᵥ (g : Fin i → K))
        exact smul_dotProduct c φ _ }
  have hG : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    refine eq_zero_of_dotProduct_gens F s hs φ (fun g hg => ?_)
    exact congrFun hφ ⟨g, hg⟩

  let ι : (s → 𝓞 K) →ₗ[ℤ] (s → K) :=
    LinearMap.pi (fun g => ((Algebra.linearMap (𝓞 K) K).restrictScalars ℤ).comp (LinearMap.proj g))
  have hle : (dualLattice F).map G ≤ LinearMap.range ι := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hv : ∀ g : s, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = φ ⬝ᵥ (g : Fin i → K) := fun g =>
      hφ g (hs ▸ Submodule.subset_span g.2)
    choose a ha using hv
    exact ⟨a, funext fun g => ha g⟩
  have hfg : ((dualLattice F).map G).FG := by
    have e : (dualLattice F).map G = (((dualLattice F).map G).comap ι).map ι := by
      rw [Submodule.map_comap_eq, inf_eq_right.mpr hle]
    rw [e]
    exact (IsNoetherian.noetherian _).map ι
  exact Submodule.fg_of_fg_map_injective G hG hfg

end DualLatticeBasisExistsAlt


open DualLatticeBasisExistsAlt in
theorem DualLatticeBasisExists.proof : DualLatticeBasisExists.Statement := by
  intro K _ _ i F
  classical
  have : Module.Finite ℤ (dualLattice F) := Module.Finite.iff_fg.mpr (dualLattice_fg F)
  exact ⟨Module.Free.ChooseBasisIndex ℤ (dualLattice F), inferInstance, inferInstance,
    ⟨Module.Free.chooseBasis ℤ (dualLattice F)⟩⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField

noncomputable section

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T] [DecidableEq T]

def dualProj (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin i → ℂ) :=
  ∑ σ : K →+* ℂ, (LinearMap.pi fun j : Fin i => LinearMap.proj (σ, j)) ∘ₗ
    (dualRecover b hb).toLinearMap ∘ₗ (LinearMap.pi fun t : T => LinearMap.proj fun _ : Unit => t)

omit [Fintype T] [DecidableEq T] in
theorem dualProj_apply (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (s : ((k : Unit) → dualBlocks T k) → ℂ) (j : Fin i) :
    dualProj b hb s j = ∑ σ : K →+* ℂ, dualRecover b hb (fun t => s fun _ => t) (σ, j) := by
  simp [dualProj]
  rfl

def dualPlanePt (b : Module.Basis T ℤ (dualLattice F)) (σ : K →+* ℂ) (v : Fin i → ℂ) :
    (Σ _ : Unit, T) → ℂ :=
  fun p => ∑ j, σ ((b p.2 : Fin i → K) j) * v j

def DualPtsOnPlane.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))),
    ∀ z ∈ mcPts (dualIdeal b), ∃ σ : K →+* ℂ, ∀ τ : K →+* ℂ, τ ≠ σ → ∀ j,
      dualRecover b hb (fun t => z ⟨(), t⟩) (τ, j) = 0

def DualPtsOfPlane.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (_hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) (v : Fin i → ℂ),
    v ≠ 0 → dualPlanePt b σ v ∈ mcPts (dualIdeal b)

def DualStdMassAt.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (D : ℕ) (F : HermLattice K (D + 1)) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))),
    (∀ σ, F.metric σ = 1) →
    ptsIntegralAt (e := D) (dualIdeal b) (dualProj b hb)
      (fun _ z => Real.log ((dualLine F b hb).h z)) (fun _ => 1) = Fintype.card (K →+* ℂ)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial Matrix NumberField

noncomputable section

def dualPointCoord {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) {K' : Type} [Field K'] [Algebra K K'] (v : Fin i → K') :
    (Σ _ : Unit, T) → K' :=
  fun p => ∑ j, algebraMap K K' ((b p.2 : Fin i → K) j) * v j

def DualCurvePoint.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (W : Ideal (MRing (dualBlocks T))),
    IsArithVar W 1 → dualIdeal b ≤ W →
      ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (v : Fin i → K'),
        v ≠ 0 ∧ W = mCoordIdeal (dualPointCoord b v)

def PointDegCPos.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K'),
    IsArithVar (mCoordIdeal y) 1 → 0 < degC (mCoordIdeal y)

def PointArInt.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (A : HermLine (fun _ : Unit => T)) (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsSectionOn (mCoordIdeal y) A s →
      (Module.finrank ℚ K' : ℝ) * arInt (mCoordIdeal y) s A (Fin.elim0 : Fin 0 → HermLine (fun _ : Unit => T)) =
        (degC (mCoordIdeal y) : ℝ) * ∑ σ : K' →+* ℂ, logNorm A s (fun p => σ (y p))

def PointVertR.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      (Module.finrank ℚ K' : ℝ) * vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → HermLine (fun _ : Unit => T)) s =
        (degC (mCoordIdeal y) : ℝ) * (Real.log |(Algebra.norm ℚ (aeval y s) : ℝ)| +
          Real.log (genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup
            (1 : Submodule (𝓞 K') K').toAddSubgroup))

def DualLineIndex.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (K' : Type) [Field K'] [NumberField K']
    [Algebra K K'] (v : Fin i → K'), v ≠ 0 →
      genIndex ((Submodule.span (𝓞 K')
          ((fun w : Fin i → K => fun j => algebraMap K K' (w j)) '' F.lattice) ⊓
          (Submodule.span K' (Set.range fun _ : Fin 1 => v)).restrictScalars (𝓞 K')).toAddSubgroup)
        (Submodule.span (𝓞 K') (Set.range fun _ : Fin 1 => v)).toAddSubgroup *
      genIndex (Submodule.span (𝓞 K') (Set.range (dualPointCoord b v))).toAddSubgroup
        (1 : Submodule (𝓞 K') K').toAddSubgroup = 1

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def DualCotangentKer.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    (_b : Module.Basis T ℤ (dualLattice F)) (k : Type) [Field k] (ρ : 𝓞 K →+* k)
    (σ : dualLattice F →+ (Fin i → k)),
    Function.Surjective ρ → Function.Surjective σ →
    (∀ (μ : 𝓞 K) (φ ψ : dualLattice F),
      (ψ : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K) → σ ψ = ρ μ • σ φ) →
    ∀ ψ : dualLattice F, σ ψ = 0 →
      ψ ∈ Submodule.span ℤ {v : dualLattice F | ∃ (μ : 𝓞 K) (φ : dualLattice F), ρ μ = 0 ∧
        (v : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K)}

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def DualLatticeIndex.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i), F'.lattice ≤ F.lattice →
    (dualLattice F).toAddSubgroup.relIndex (dualLattice F').toAddSubgroup =
      F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup

end

end GroundTheory.Heights₂.Heights
end
