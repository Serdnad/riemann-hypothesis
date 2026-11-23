module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle023
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder

noncomputable section

def DualEnergyCharts.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ i →
    ∃ A : (K →+* ℂ) → Matrix (Fin i) (Fin (i - 1 + 1)) ℂ, (∀ σ, Function.Bijective (A σ).mulVec) ∧
      ∀ k : ℕ,
        ptsIntegral (dualIdeal b)
            (pot fun j : Fin (i - 1) =>
              if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
            (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) =
          ∑ σ : K →+* ℂ, chartMixedEnergy ((A σ)ᴴ * F.metric σ * A σ) ((A σ)ᴴ * A σ) k

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

namespace VerticalPointInjective

theorem coord_ne_zero {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K') (t : T)
    (ht : (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ mCoordIdeal y) : y ⟨(), t⟩ ≠ 0 := by
  intro h0
  apply ht
  simp [mCoordIdeal, mConeMap, RingHom.mem_ker, h0]

theorem isMultiHomogIdeal_of_mem_divSupp {T : Type} [Fintype T] {K' : Type} [Field K']
    (y : (Σ _ : Unit, T) → K') (s : MRing (fun _ : Unit => T)) (hA : IsArithVar (mCoordIdeal y) 1)
    (hs : IsMultiHomog s (fun _ => 1)) {W : Ideal (MRing (fun _ : Unit => T))}
    (hW : W ∈ divSupp (mCoordIdeal y) s) : IsMultiHomogIdeal W := by
  have hP : NumbersDVR.IsMultiHomogIdeal (mCoordIdeal y) :=
    (Bridge.isMultiHomogIdeal_iff _).2 hA.2.1.2.1
  have hJ := NumbersDVR.SupSpanMultiHomog.full.{0} ℤ Unit (fun _ => T) (mCoordIdeal y) s (fun _ => 1) hP
    ((Bridge.isMultiHomog_iff s _).2 hs)
  exact (Bridge.isMultiHomogIdeal_iff _).1
    (NumbersDVR.MinimalPrimeMultiHomog.full.{0} ℤ Unit (fun _ => T) _ W hJ hW.1)

end VerticalPointInjective


open VerticalPointInjective in
theorem VertPointInj.proof (hCh : VertPointChart.Statement) : VertPointInj.Statement := by
  intro T _ K' _ _ y s hA hs hsP W hW W' hW' hWW'
  obtain ⟨t, ht⟩ := hW.2 ()
  obtain ⟨t', ht'⟩ := hW'.2 ()
  have hyt : y ⟨(), t⟩ ≠ 0 :=
    VerticalPointInjective.coord_ne_zero y t fun h => ht (le_sup_left.trans hW.1.1.2 h)
  obtain ⟨hmax, hrat, hform⟩ := hCh T K' y s hA hs hsP W hW t ht
  obtain ⟨-, -, hform'⟩ := hCh T K' y s hA hs hsP W' hW' t' ht'
  obtain ⟨a', b', hb', hab'⟩ := hrat t'
  have hab'' : (b' : K') * y ⟨(), t'⟩ = a' * y ⟨(), t⟩ := by
    rw [← hab']; field_simp
  have hle : W' ≤ W := by
    obtain ⟨S, hS, hSeq⟩ := VerticalPointInjective.isMultiHomogIdeal_of_mem_divSupp y s hA hs hW'
    rw [hSeq, Ideal.span_le]
    intro g hg
    obtain ⟨e, he⟩ := hS g hg
    have he' : IsMultiHomog g (fun _ => e ()) := by
      have : e = fun _ => e () := funext fun u => by cases u; rfl
      rwa [this] at he
    obtain ⟨a, b, ha, hb, habg⟩ := (hform' (e ()) g he').1 (hSeq ▸ Ideal.subset_span hg)
    rw [← hWW'] at ha hb
    refine (hform (e ()) g he').2 ⟨a * a' ^ e (), b' ^ e () * b, Ideal.mul_mem_right _ _ ha, ?_, ?_⟩
    · intro h
      rcases hmax.isPrime.mem_or_mem h with h | h
      · exact hb' (hmax.isPrime.mem_of_pow_mem _ h)
      · exact hb h
    · push_cast
      calc (b' : K') ^ e () * b * aeval y g = a * ((b' : K') * y ⟨(), t'⟩) ^ e () := by
            rw [mul_assoc, habg]; ring
        _ = _ := by rw [hab'']; ring
  exact le_antisymm (hW.1.2 ⟨hW'.1.1.1, hW'.1.1.2⟩ hle) hle

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial

noncomputable section

abbrev dualStdModelField (K : Type) [Field K] (i : ℕ) : Type :=
  FractionRing (MvPolynomial Unit (MvPolynomial Unit (ProjField K i)))

def dualStdModelS (K : Type) [Field K] (i : ℕ) : dualStdModelField K i :=
  algebraMap (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) _ (C (X ()))

def dualStdModelT (K : Type) [Field K] (i : ℕ) : dualStdModelField K i :=
  algebraMap (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) _ (X ())

def dualStdModelEmb (K : Type) [Field K] (i : ℕ) : ProjField K i →+* dualStdModelField K i :=
  (algebraMap (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) _).comp
    ((C : MvPolynomial Unit (ProjField K i) →+* _).comp C)

def dualStdModelPt {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) :
    (Σ k, Sum.elim (dualBlocks T) (PBlk i) k) → dualStdModelField K i
  | ⟨Sum.inl (), t⟩ => dualStdModelEmb K i (dualLatticeCoord b ⟨(), t⟩) * dualStdModelS K i
  | ⟨Sum.inr (), j⟩ =>
    dualStdModelEmb K i (algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X j)) * dualStdModelS K i *
      dualStdModelT K i

def GenFibreModelTransport.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type)
    [∀ k, Fintype (ι' k)] (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (G : GenFibre v P')
    (Ω : Type) [Field Ω] (z : (Σ k', ι' k') → Ω), RingHom.ker (eval₂Hom (Int.castRingHom Ω) z : MRing ι' →+* Ω) = P' →
    ∀ (Φ₀ : Type) [Field Φ₀] [Algebra Φ₀ Ω], (algebraMap Φ₀ Ω).fieldRange = Subfield.closure (Set.range (z ∘ v)) →
    ∀ (τ : Type) (w : τ → Σ k', ι' k') (q : Σ k', ι' k'),
      (G.x' q = 0 ↔ z q = 0) ∧
      Module.finrank G.Φ (Algebra.adjoin G.Φ (Set.range fun t => G.x' (w t) / G.x' q)) =
        Module.finrank Φ₀ (Algebra.adjoin Φ₀ (Set.range fun t => z (w t) / z q)) ∧
      (Transcendental (Algebra.adjoin G.Φ (Set.range fun t => G.x' (w t) / G.x' q)) (G.x' q) ↔
        Transcendental (Algebra.adjoin Φ₀ (Set.range fun t => z (w t) / z q)) (z q))

def DualStdGraphModel.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))),
    RingHom.ker (eval₂Hom (Int.castRingHom (dualStdModelField K i)) (dualStdModelPt b) :
        MRing (Sum.elim (dualBlocks T) (PBlk i)) →+* dualStdModelField K i) =
      graphIdeal (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))

def DualStdModelRank.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (Φ₀ : Type) [Field Φ₀] [Algebra Φ₀ (dualStdModelField K i)],
    (algebraMap Φ₀ (dualStdModelField K i)).fieldRange =
      Subfield.closure (Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i))) →
    1 ≤ i → ∀ c : T,
      dualStdModelPt b (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) ≠ 0 ∧
      Module.finrank Φ₀ (Algebra.adjoin Φ₀ (Set.range fun t : T =>
        dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
          dualStdModelPt b (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))) = Module.finrank ℚ K

def DualStdModelTransc.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (Φ₀ : Type) [Field Φ₀] [Algebra Φ₀ (dualStdModelField K i)],
    (algebraMap Φ₀ (dualStdModelField K i)).fieldRange =
      Subfield.closure (Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i))) →
    1 ≤ i → ∀ c : T,
      Transcendental (Algebra.adjoin Φ₀ (Set.range fun t : T =>
        dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
          dualStdModelPt b (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)))
        (dualStdModelPt b (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

def IntCoordArInt.Statement : Prop :=
  ∀ (T T₂ : Type) [Fintype T] [DecidableEq T] [Fintype T₂] [DecidableEq T₂] (A : Matrix T T₂ ℤ)
    (B : Matrix T₂ T ℤ) (_ : A * B = 1) (hBA : B * A = 1) (Q : Ideal (MRing (dualBlocks T))) (e : ℕ)
    (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T))
    (Ab : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)) (s : MRing (dualBlocks T)),
    IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm Ab → IsSectionOn Q Ab s →
    arInt (Q.comap (intCoordSubst A)) (intCoordSubst B s) (intCoordLine B ⟨A, hBA⟩ Ab)
        (fun j => intCoordLine B ⟨A, hBA⟩ (L j)) =
      arInt Q s Ab L

def intCoordSwap : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

theorem intCoordSwap_mul_self : intCoordSwap * intCoordSwap = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [intCoordSwap, Matrix.mul_apply, Fin.sum_univ_two]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial

noncomputable section

def OneBlockPointDeg.Statement : Prop :=
  ∀ (Φ Φ' : Type) [Field Φ] [Field Φ'] [Algebra Φ Φ'] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (k₀ : K), (∀ k, k = k₀) →
    ∀ (w : (Σ k, ι k) → Φ') (c : ∀ k, ι k), w ⟨k₀, c k₀⟩ ≠ 0 →
      Module.Finite Φ (Algebra.adjoin Φ (Set.range fun p => w p / w ⟨k₀, c k₀⟩)) →
      Transcendental (Algebra.adjoin Φ (Set.range fun p => w p / w ⟨k₀, c k₀⟩)) (w ⟨k₀, c k₀⟩) →
      IsProjVarF (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) 0 ∧
        IsChart (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) c ∧
        ptDeg (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) c =
          Module.finrank Φ (Algebra.adjoin Φ (Set.range fun p => w p / w ⟨k₀, c k₀⟩))

def DualStdFibreRatios.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (G : GenFibre (inrV (ι := dualBlocks T) (ι₂ := PBlk i))
      (graphIdeal (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b)))),
    1 ≤ i → ∃ c : T,
      G.x' (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) ≠ 0 ∧
      Module.finrank G.Φ (Algebra.adjoin G.Φ (Set.range fun t : T =>
        G.x' (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
          G.x' (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))) = Module.finrank ℚ K ∧
      Transcendental (Algebra.adjoin G.Φ (Set.range fun t : T =>
        G.x' (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
          G.x' (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)))
        (G.x' (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

def IntCoordGeoNum.Statement : Prop :=
  ∀ (T T₂ : Type) [Fintype T] [DecidableEq T] [Fintype T₂] [DecidableEq T₂] (A : Matrix T T₂ ℤ)
    (B : Matrix T₂ T ℤ), A * B = 1 → B * A = 1 →
    ∀ (V : Ideal (MRing (dualBlocks T))) (n p : ℕ), IsMultiProjPrime V → p.Prime →
      (C (p : ℤ) : MRing (dualBlocks T)) ∈ V →
      ringKrullDim (MRing (dualBlocks T) ⧸ V) = ((n + Fintype.card Unit : ℕ) : WithBot ℕ∞) →
      ∀ a : Fin n → Unit → ℤ, geoNum n (V.comap (intCoordSubst A)) a = geoNum n V a

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix

noncomputable section

namespace DualCotangentKernel

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem smul_mem (F : HermLattice K i) (μ : 𝓞 K) {φ : Fin i → K} (hφ : φ ∈ dualLattice F) :
    (algebraMap (𝓞 K) K μ) • φ ∈ dualLattice F := by
  intro x hx
  rw [smul_dotProduct, smul_eq_mul]
  obtain ⟨r, hr⟩ := hφ x hx
  exact ⟨μ * r, by rw [map_mul, hr]⟩

def mulMap (F : HermLattice K i) (c : 𝓞 K) : dualLattice F →ₗ[ℤ] dualLattice F where
  toFun χ := ⟨algebraMap (𝓞 K) K c • (χ : Fin i → K), smul_mem F c χ.2⟩
  map_add' χ χ' := by ext1; simp [smul_add]
  map_smul' n χ := by
    ext1
    show algebraMap (𝓞 K) K c • ((n • χ : dualLattice F) : Fin i → K) =
      n • (algebraMap (𝓞 K) K c • (χ : Fin i → K))
    rw [Submodule.coe_smul, smul_comm]

def prodSet (F : HermLattice K i) {k : Type} [Field k] (ρ : 𝓞 K →+* k) : Set (dualLattice F) :=
  {v | ∃ (μ : 𝓞 K) (φ : dualLattice F), ρ μ = 0 ∧
    (v : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K)}

theorem mulMap_mem (F : HermLattice K i) {k : Type} [Field k] (ρ : 𝓞 K →+* k) (c : 𝓞 K)
    {χ : dualLattice F} (hχ : χ ∈ Submodule.span ℤ (prodSet F ρ)) :
    mulMap F c χ ∈ Submodule.span ℤ (prodSet F ρ) := by
  have hle : Submodule.span ℤ (prodSet F ρ) ≤ (Submodule.span ℤ (prodSet F ρ)).comap (mulMap F c) := by
    rw [Submodule.span_le]
    rintro v ⟨μ, φ, hμ, hv⟩
    refine Submodule.subset_span ⟨c * μ, φ, by rw [map_mul, hμ, mul_zero], ?_⟩
    show algebraMap (𝓞 K) K c • (v : Fin i → K) = _
    rw [hv, smul_smul, ← map_mul]
  exact hle hχ

end DualCotangentKernel


open DualCotangentKernel in
theorem DualCotangentKer.proof : DualCotangentKer.Statement := by
  intro K _ _ i F T _ _b k _ ρ σ hρ hσ hsl ψ hψ
  classical
  change ψ ∈ Submodule.span ℤ (prodSet F ρ)

  choose φ hφ using fun j : Fin i => hσ (Pi.single j 1)
  let w : Option (Fin i) → dualLattice F := fun o => o.elim ψ φ

  have hdep : ¬ LinearIndependent K (fun o => (w o : Fin i → K)) := by
    intro h
    have := h.fintype_card_le_finrank
    rw [Fintype.card_option, Fintype.card_fin, Module.finrank_fin_fun] at this
    omega
  obtain ⟨g, hg, o, ho⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hJ : RingHom.ker ρ ≠ ⊤ := RingHom.ker_ne_top ρ
  obtain ⟨a, hint, o', -, hnot⟩ :=
    Ideal.exist_integer_multiples_notMem (A := 𝓞 K) (K := K) hJ Finset.univ g (Finset.mem_univ o) ho
  choose c hc using fun x => hint x (Finset.mem_univ x)

  let χ : Option (Fin i) → dualLattice F := fun x => mulMap F (c x) (w x)
  have hsum : ∑ x, χ x = 0 := by
    ext1
    rw [Submodule.coe_sum, Submodule.coe_zero]
    calc ∑ x, ((χ x : dualLattice F) : Fin i → K) = ∑ x, algebraMap (𝓞 K) K (c x) • (w x : Fin i → K) := rfl
      _ = a • ∑ x, g x • (w x : Fin i → K) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hc x, smul_smul]
      _ = 0 := by rw [hg, smul_zero]
  have hσχ : ∀ x, σ (χ x) = ρ (c x) • σ (w x) := fun x => hsl (c x) (w x) (χ x) rfl
  have hσsum : ∑ x, ρ (c x) • σ (w x) = 0 := by

    rw [← map_zero σ, ← hsum, map_sum]
    exact Finset.sum_congr rfl fun x _ => (hσχ x).symm

  have hsome : ∀ j, ρ (c (some j)) = 0 := by
    intro j
    have h := congrFun hσsum j
    rw [Fintype.sum_option] at h
    simp only [w, Option.elim_none, Option.elim_some, hψ, smul_zero, zero_add, hφ, Finset.sum_apply,
      Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Pi.zero_apply] at h
    rw [Finset.sum_ite_eq] at h
    simpa using h
  have hnone : ρ (c none) ≠ 0 := by
    intro h0
    apply hnot
    rw [FractionalIdeal.mem_coeIdeal]
    refine ⟨c o', ?_, hc o'⟩
    rw [RingHom.mem_ker]
    cases o' with
    | none => exact h0
    | some j => exact hsome j

  have hgen : ∀ j, χ (some j) ∈ Submodule.span ℤ (prodSet F ρ) := fun j =>
    Submodule.subset_span ⟨c (some j), φ j, hsome j, rfl⟩
  have hχ0 : χ none ∈ Submodule.span ℤ (prodSet F ρ) := by
    have h : χ none = -∑ j, χ (some j) := by
      rw [Fintype.sum_option] at hsum
      exact eq_neg_of_add_eq_zero_left hsum
    rw [h]
    exact neg_mem (Submodule.sum_mem _ fun j _ => hgen j)

  obtain ⟨bb, hbb⟩ := hρ (ρ (c none))⁻¹
  have hm : ρ (bb * c none - 1) = 0 := by
    rw [map_sub, map_mul, hbb, inv_mul_cancel₀ hnone, map_one, sub_self]
  have h1 : mulMap F bb (χ none) ∈ Submodule.span ℤ (prodSet F ρ) := mulMap_mem F ρ bb hχ0
  have h2 : mulMap F (bb * c none - 1) ψ ∈ Submodule.span ℤ (prodSet F ρ) :=
    Submodule.subset_span ⟨_, ψ, hm, rfl⟩
  have hψeq : ψ = mulMap F bb (χ none) - mulMap F (bb * c none - 1) ψ := by
    ext1
    simp only [χ, w, Option.elim_none, mulMap, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sub,
      smul_smul, ← map_mul, ← sub_smul, map_sub, map_one]
    rw [sub_sub_cancel, one_smul]
  rw [hψeq]
  exact sub_mem h1 h2

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

def DualMetricEnergy.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ i →
    ∑ k ∈ Finset.range i,
        ptsIntegral (dualIdeal b)
          (pot fun j : Fin (i - 1) =>
            if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
          (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) =
      1 / 2 * (∑ σ : K →+* ℂ, Real.log (F.metric σ).det.re) *
        geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

end

end GroundTheory.Heights₂.Heights
end
