module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle871
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1375
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1363
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open scoped TensorProduct Kronecker

noncomputable section

open Formalism.BasicNotions.TH MvPolynomial

namespace GlobalTheory.KFixIrr.LowStable

theorem deg_X_pderiv {σ : Type} (a b : σ) (P : MvPolynomial σ ℂ) :
    (X a * pderiv b P).totalDegree ≤ P.totalDegree := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [P.as_sum, map_sum, Finset.mul_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [pderiv_monomial]
  by_cases h : s b = 0
  · simp [h]
  · refine le_trans ?_ (le_totalDegree hs)
    rw [X, monomial_mul]
    refine (totalDegree_monomial_le _ _).trans (le_of_eq ?_)
    have h1 : s = Finsupp.single b 1 + (s - Finsupp.single b 1) := by
      rw [add_tsub_cancel_of_le]
      exact Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h)
    conv_rhs => rw [h1]
    rw [Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_add_index' (by simp) (by simp)]
    simp [Function.id_def]

theorem deg_pderiv_X {σ : Type} (a b : σ) (P : MvPolynomial σ ℂ) :
    (pderiv b (X a * P)).totalDegree ≤ P.totalDegree := by
  classical
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  refine (totalDegree_add _ _).trans (max_le (deg_X_pderiv _ _ _) ?_)
  rw [pderiv_X, Pi.single_apply]
  split_ifs <;> simp

def nonRaising (σ : Type) : Submodule ℂ (Module.End ℂ (MvPolynomial σ ℂ)) where
  carrier := {L | ∀ P, (L P).totalDegree ≤ P.totalDegree}
  add_mem' {L L'} h h' P := (totalDegree_add _ _).trans (max_le (h P) (h' P))
  zero_mem' P := by simp
  smul_mem' c L h P := (totalDegree_smul_le _ _).trans (h P)

theorem mem_nonRaising {σ : Type} {L : Module.End ℂ (MvPolynomial σ ℂ)} :
    L ∈ nonRaising σ ↔ ∀ P, (L P).totalDegree ≤ P.totalDegree := Iff.rfl

theorem rl_pos {P Q R S : ℕ} (l l' : Ln P Q R S) (hl : linePos l = true) (hl' : linePos l' = true) :
    raiB l * lowB l' ∈ nonRaising (Ln P Q R S) := by
  refine mem_nonRaising.2 fun g => ?_
  rw [Module.End.mul_apply, raiB, lowB, if_pos hl, if_pos hl', LinearMap.mulLeft_apply, Derivation.coeFn_coe]
  exact deg_X_pderiv _ _ _

theorem rl_neg {P Q R S : ℕ} (l l' : Ln P Q R S) (hl : linePos l = false) (hl' : linePos l' = false) :
    raiB l * lowB l' ∈ nonRaising (Ln P Q R S) := by
  refine mem_nonRaising.2 fun g => ?_
  rw [Module.End.mul_apply, raiB, lowB, if_neg (by simp [hl]), if_neg (by simp [hl']), LinearMap.mulLeft_apply,
    LinearMap.neg_apply, Derivation.coeFn_coe, totalDegree_neg]
  exact deg_pderiv_X _ _ _

theorem omE_mem {P Q R S : ℕ} (l l' : Ln P Q R S) (h : linePos l = linePos l') :
    omE l l' ∈ nonRaising (Ln P Q R S) := by
  rw [omE]
  refine Submodule.add_mem _ ?_ ?_
  · cases hl : linePos l
    · exact rl_neg l l' hl (h ▸ hl)
    · exact rl_pos l l' hl (h ▸ hl)
  · split_ifs
    · exact Submodule.smul_mem _ _ (mem_nonRaising.2 fun g => le_rfl)
    · exact Submodule.zero_mem _

theorem linePos_same {P Q R S : ℕ} (a : Ix P Q) (c d : Ix R S) (h : sameBlock c d) :
    linePos ((a, c) : Ln P Q R S) = linePos (a, d) := by
  rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;> simp_all [sameBlock, linePos]

theorem fockAct2_mem {P Q R S : ℕ} (Z : Mat R S) (hZ : IsKC Z) :
    fockAct2 P Q R S Z ∈ nonRaising (Ln P Q R S) := by
  classical
  rw [show fockAct2 P Q R S Z = omAct P Q R S ((1 : Mat P Q) ⊗ₖ Z) from rfl, omAct_apply]
  refine Submodule.sum_mem _ fun l _ => Submodule.sum_mem _ fun l' _ => ?_
  rcases l with ⟨a, c⟩
  rcases l' with ⟨a', d⟩
  rw [Matrix.kroneckerMap_apply]
  by_cases ha : a = a'
  · subst ha
    by_cases hcd : sameBlock c d
    · exact Submodule.smul_mem _ _ (omE_mem _ _ (linePos_same a c d hcd))
    · rw [hZ c d hcd, mul_zero, zero_smul]; exact Submodule.zero_mem _
  · rw [Matrix.one_apply_ne ha, zero_mul, zero_smul]; exact Submodule.zero_mem _

theorem fockAct2_lowOne : ∀ (P Q R S : ℕ) (x : ℚ) (d : ℕ) (Z : Formalism.BasicNotions.TH.Mat R S), Formalism.BasicNotions.TH.IsKC Z →
    ∀ f ∈ GlobalTheory.KFixIrr.lowOne P Q R S x d, Formalism.BasicNotions.TH.fockAct2 P Q R S Z f ∈ GlobalTheory.KFixIrr.lowOne P Q R S x d := by
  intro P Q R S x d Z hZ f hf
  rw [mem_lowOne] at hf ⊢
  refine ⟨?_, (mem_nonRaising.1 (fockAct2_mem Z hZ) f).trans hf.2⟩
  rw [mem_chiOne] at hf ⊢
  intro X hX
  have h := LinearMap.congr_fun ((GlobalTheory.FockPair.pair_lie_commute P Q R S).2.2 X Z) f
  simp only [Module.End.mul_apply] at h
  rw [h, hf.1 X hX, map_smul]

end GlobalTheory.KFixIrr.LowStable

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.ConjFull

open GlobalTheory.ConjDim

variable {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar}

theorem conjMap_mem_mult (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w))
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ)
    {J : Set (GA D V)} {χ χ' : GA D V → ℂ} (hχ : ∀ k ∈ J, χ' k = star (χ k)) {T : MMap M} (hT : T ∈ Mult θ M J χ) :
    conjMap M M' c h T ∈ Mult θ M' J χ' := by
  obtain ⟨T', hT', e1⟩ := (GlobalTheory.T.complexConjugation_maps_multiplicitySpace θ M M' c hc).2 J χ T hT
  have : conjMap M M' c h T = T' := by
    refine MultilinearMap.ext fun v' => funext fun g => ?_
    rw [e1 v' (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (fun _ => rfl) g]
    rfl
  rw [this]
  exact mult_congr θ M' hχ hT'

theorem heckeLin_star (R : Finset (GA D V)) (φ : GA D V → ℂ) : heckeLin V R (star φ) = star (heckeLin V R φ) := by
  funext g
  show ∑ γ ∈ R, star (φ (g * γ)) = star (∑ γ ∈ R, φ (g * γ))
  rw [star_sum]

theorem rank_le (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w))
    (J J0 : Set (GA D V)) (χ χ' χ0 : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ))
    (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (a a' : Pl D.host.E → List ℤ → ℂ)
    (hχ : ∀ k ∈ J, χ' k = star (χ k)) (hχ0 : ∀ k ∈ J0, χ0 k = star (χ0 k))
    (he : ∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) (ha : ∀ P d, a' P d = star (a P d)) :
    Module.rank ℂ (goodPart θ M J χ e ⊓ partFull θ M J0 χ0 SF a : Submodule ℂ (MMap M)) ≤
      Module.rank ℂ (goodPart θ M' J χ' e' ⊓ partFull θ M' J0 χ0 SF a' : Submodule ℂ (MMap M')) := by
  have h := (GlobalTheory.T.complexConjugation_maps_multiplicitySpace θ M M' c hc).1
  have key : ∀ T ∈ (goodPart θ M J χ e ⊓ partFull θ M J0 χ0 SF a : Submodule ℂ (MMap M)),
      conjMap M M' c h T ∈ (goodPart θ M' J χ' e' ⊓ partFull θ M' J0 χ0 SF a' : Submodule ℂ (MMap M')) := by
    rintro T ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨conjMap_mem_mult θ M M' c hc h hχ h1, ?_⟩, ?_⟩
    · have h2' : ∀ v, e (T v) = T v := fun v => by
        have := congrArg (fun U : MMap M => U v) (sub_eq_zero.1 (LinearMap.mem_ker.1 h2))
        exact this
      refine LinearMap.mem_ker.2 (sub_eq_zero.2 (MultilinearMap.ext fun v' => ?_))
      show e' (conjMap M M' c h T v') = conjMap M M' c h T v'
      rw [conjMap_apply, he, h2']
    · obtain ⟨h4, h5⟩ := (mem_partFull θ M J0 χ0 SF a T).1 h3
      refine (mem_partFull θ M' J0 χ0 SF a' _).2 ⟨conjMap_mem_mult θ M M' c hc h hχ0 h4, fun P d R hR v' => ?_⟩
      rw [conjMap_apply, heckeLin_star, h5 P d R hR, star_smul, ha]
  let j : (goodPart θ M J χ e ⊓ partFull θ M J0 χ0 SF a : Submodule ℂ (MMap M)) →+
      (goodPart θ M' J χ' e' ⊓ partFull θ M' J0 χ0 SF a' : Submodule ℂ (MMap M')) :=
    AddMonoidHom.mk' (fun T => ⟨conjMap M M' c h T, key T T.2⟩) fun T T' =>
      Subtype.ext (MultilinearMap.ext fun v' => star_add _ _)
  refine rank_le_of_injective_injective (star : ℂ → ℂ) j (fun r hr => star_eq_zero.1 hr) ?_ ?_
  · refine (injective_iff_map_eq_zero j).2 fun T hT => Subtype.ext ?_
    exact conjMap_eq_zero M M' c h T (congrArg Subtype.val hT)
  · intro r T
    refine Subtype.ext (MultilinearMap.ext fun v' => ?_)
    show star (star r • (T : MMap M) _) = r • star ((T : MMap M) _)
    rw [star_smul, star_star]

theorem conj_rank_full : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → ∀ (J J0 : Set (GA D V)) (χ χ' χ0 : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (a : Pl D.host.E → List ℤ → ℂ), (∀ k ∈ J, χ' k = star (χ k)) → (∀ k ∈ J0, χ0 k = star (χ0 k)) → (∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) → Module.rank ℂ (goodPart θ M J χ e ⊓ partFull θ M J0 χ0 SF a : Submodule ℂ (MMap M)) = Module.rank ℂ (goodPart θ M' J χ' e' ⊓ partFull θ M' J0 χ0 SF (fun P d => star (a P d)) : Submodule ℂ (MMap M')) := by
  intro D V S S' θ M M' c hc J J0 χ χ' χ0 e e' SF a hχ hχ0 he
  refine le_antisymm (rank_le θ M M' c hc J J0 χ χ' χ0 e e' SF a _ hχ hχ0 he fun _ _ => rfl) ?_
  refine rank_le θ M' M (fun τ => (c τ).symm) ?_ J J0 χ' χ χ0 e' e SF _ a ?_ hχ0 ?_ ?_
  · intro τ g hg w
    apply (c τ).injective
    rw [hc τ g hg]
    simp
  · intro k hk
    rw [hχ k hk, star_star]
  · intro φ
    rw [← star_star φ, he, star_star, star_star]
  · intro P d
    simp

end GlobalTheory.ConjFull

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

noncomputable section

namespace GlobalTheory.ThetaScaledNe

theorem normAtPlace_le_norm {F : Type} [Field F] [NumberField F] (w : InfinitePlace F)
    (y : mixedEmbedding.mixedSpace F) : mixedEmbedding.normAtPlace w y ≤ ‖y‖ := by
  by_cases hw : w.IsReal
  · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw]
    exact (norm_le_pi_norm _ _).trans (norm_fst_le _)
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    rw [mixedEmbedding.normAtPlace_apply_of_isComplex hc]
    exact (norm_le_pi_norm _ _).trans (norm_snd_le _)

theorem one_le_norm_mixedEmbedding {F : Type} [Field F] [NumberField F] {y : 𝓞 F} (hy : y ≠ 0) :
    1 ≤ ‖mixedEmbedding F (y : F)‖ := by
  by_contra h
  push_neg at h
  have hlt : ∀ z : InfinitePlace F, z (y : F) < 1 := fun z => by
    have := normAtPlace_le_norm z (mixedEmbedding F (y : F))
    rw [mixedEmbedding.normAtPlace_apply] at this
    exact this.trans_lt h
  let w : InfinitePlace F := Classical.arbitrary _
  have := InfinitePlace.one_le_of_lt_one (w := w) hy (fun z _ => hlt z)
  exact absurd (hlt w) (not_lt.mpr this)

theorem exists_int_of_mem_scaledInt {F : Type} [Field F] [NumberField F] {κ : Type} {a : F} (ha : a ≠ 0)
    {ξ : κ → F} (h : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a)
    (i : κ) : ∃ y : 𝓞 F, ξ i = a * (y : F) := by
  have hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (a⁻¹ * ξ i) ≤ 1 := fun v => by
    have h1 := h i v
    have e : (algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) v = algebraMap F (v.adicCompletion F) (ξ i) := rfl
    rw [e, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀] at h1
    rw [Valuation.map_mul, map_inv₀]
    have e1 : Valued.v (algebraMap F (v.adicCompletion F) a) = v.valuation F a :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
    have e2 : Valued.v (algebraMap F (v.adicCompletion F) (ξ i)) = v.valuation F (ξ i) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (ξ i)
    rw [e1, e2] at h1
    exact h1
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hv
  refine ⟨y, ?_⟩
  have hy' : (y : F) = a⁻¹ * ξ i := hy
  rw [hy', mul_inv_cancel_left₀ ha]

theorem exists_thetaSum_scaledInt_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∃ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      thetaSum F (pureA F f ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator
        (fun _ => (1 : ℂ)))) ≠ 0 := by
  intro F _ _ κ _ a ha
  let V := κ → mixedEmbedding.mixedSpace F
  set c : mixedEmbedding.mixedSpace F := mixedEmbedding F a⁻¹ with hc
  set ε : ℝ := 1 / (‖c‖ + 1) with hε
  have hε0 : 0 < ε := by positivity
  let b : ContDiffBump (0 : V) := ⟨ε / 2, ε, half_pos hε0, half_lt_self hε0⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let f : SchwartzMap V ℂ := h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hf : ∀ x, f x = ((b x : ℝ) : ℂ) := fun x => rfl
  refine ⟨f, ?_⟩
  set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
    (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)) with hg
  have hzero : ∀ ξ : κ → F, ξ ≠ 0 → pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = 0 := by
    intro ξ hξ
    rw [pureA_algebraMap]
    by_cases hm : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a
    · refine mul_eq_zero_of_left ?_ _
      obtain ⟨i, hi⟩ : ∃ i, ξ i ≠ 0 := by
        by_contra h; push_neg at h; exact hξ (funext h)
      obtain ⟨y, hy⟩ := exists_int_of_mem_scaledInt ha hm i
      have hy0 : y ≠ 0 := by
        rintro rfl
        exact hi (by simpa using hy)
      have hn1 := one_le_norm_mixedEmbedding hy0
      have e : mixedEmbedding F (y : F) = c * mixedEmbedding F (ξ i) := by
        rw [hc, ← map_mul, hy, inv_mul_cancel_left₀ ha]
      have h2 : ‖mixedEmbedding F (ξ i)‖ ≤ ‖(fun j => mixedEmbedding F (ξ j) : V)‖ :=
        norm_le_pi_norm (fun j => mixedEmbedding F (ξ j)) i
      have h3 : 1 ≤ ‖c‖ * ‖(fun j => mixedEmbedding F (ξ j) : V)‖ := by
        rw [e] at hn1
        exact hn1.trans ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)))
      rw [hf, b.zero_of_le_dist, Complex.ofReal_zero]
      show ε ≤ dist (fun j => mixedEmbedding F (ξ j) : V) 0
      rw [dist_zero_right, hε, div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg c, norm_nonneg (fun j => mixedEmbedding F (ξ j) : V)]
    · refine mul_eq_zero_of_right _ ?_
      rw [hg]
      exact Set.indicator_of_notMem hm _
  have h0 : pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((0 : κ → F) i)) = 1 := by
    rw [pureA_algebraMap]
    have hx : (fun i : κ => mixedEmbedding F ((0 : κ → F) i)) = 0 := by
      funext i; exact map_zero _
    have hm : (fun i : κ => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((0 : κ → F) i)) ∈
        GlobalTheory.EvAdm.scaledInt F κ a := by
      have e : (fun i : κ => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((0 : κ → F) i)) = 0 := by
        funext i; exact map_zero _
      rw [e]; exact zero_mem _
    rw [hx, hf, b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hε0).le), hg,
      Set.indicator_of_mem hm]
    simp
  show (∑' ξ : κ → F, pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ≠ 0
  rw [tsum_eq_single 0 hzero, h0]
  exact one_ne_zero

end GlobalTheory.ThetaScaledNe

end
end

section

namespace MongeAmpereTransport
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MaTransport

variable {e : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']

def carryPartition (A : FinHolAtlas e X) (h : X ≃ₜ X') (P : ChartPartition A) :
    ChartPartition (tAtlas A h) where
  χ j := P.χ j ∘ h.symm
  smooth j k := by
    have e₁ : (P.χ j ∘ h.symm) ∘ ((tAtlas A h).chart k).symm = P.χ j ∘ (A.chart k).symm :=
      funext fun y => by simp [tAtlas_symm]
    rw [e₁]
    exact P.smooth j k
  nonneg j x := P.nonneg j _
  tsupport_subset j := fun x hx =>
    P.tsupport_subset j (tsupport_comp_subset_preimage (P.χ j) h.symm.continuous hx)
  sum_eq_one x := P.sum_eq_one (h.symm x)

theorem isPotential_pullback (A : FinHolAtlas e X) (h : X ≃ₜ X') {Q : LocPot X'}
    (hQ : IsPotential (tAtlas A h) Q) : IsPotential A (Q.pullback h h.continuous) := by
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · exact hQ.1 (h x) j
  · obtain ⟨W, hW, hyW, G, hG, hd⟩ := hQ.2 (h x) (h x') (h y) hy
    refine ⟨h ⁻¹' W, hW.preimage h.continuous, hyW, G ∘ h, fun j => ?_, fun z hz => ?_⟩
    · exact hG j
    · exact hd (h z) hz

theorem integralWith_carry (A : FinHolAtlas e X) (h : X ≃ₜ X') (P : ChartPartition A)
    (Φ : Fin e → LocPot X') (g : X' → ℝ) :
    integralWith (tAtlas A h) (carryPartition A h P) Φ g =
      integralWith A P (fun i => (Φ i).pullback h h.continuous) (g ∘ h) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change P.χ j (h.symm (h ((A.chart j).symm y))) * g (h ((A.chart j).symm y)) * _ =
    P.χ j ((A.chart j).symm y) * g (h ((A.chart j).symm y)) * _
  rw [h.symm_apply_apply]
  rfl

theorem mInt_tAtlas (e : ℕ) (X X' : Type) [TopologicalSpace X] [TopologicalSpace X'] [CompactSpace X]
    [T2Space X] [CompactSpace X'] [T2Space X'] (A : FinHolAtlas e X) (h : X ≃ₜ X')
    (Φ : Fin e → LocPot X') (g : X' → ℝ) (hΦ : ∀ i, IsPotential (tAtlas A h) (Φ i))
    (hg : Continuous g) :
    mInt (tAtlas A h) Φ g = mInt A (fun i => (Φ i).pullback h h.continuous) (g ∘ h) := by
  obtain ⟨P⟩ := existsPartition A
  have hΨ : ∀ i, IsPotential A ((Φ i).pullback h h.continuous) :=
    fun i => isPotential_pullback A h (hΦ i)
  rw [mIntEq (tAtlas A h) (carryPartition A h P) Φ hΦ g (mIntegrableCont _ Φ hΦ g hg),
    mIntEq A P _ hΨ (g ∘ h) (mIntegrableCont A _ hΨ _ (hg.comp h.continuous)),
    integralWith_carry]

end GlobalTheory.CompanionTheory.MaTransport

end
end

end MongeAmpereTransport
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
theorem _root_.GlobalTheory.Adopt.mongeAmpereIntegral_invariant_homeomorph_transport : ∀ (e : ℕ) (X X' : Type) [TopologicalSpace X] [TopologicalSpace X'] [CompactSpace X] [T2Space X] [CompactSpace X'] [T2Space X'] (A : FinHolAtlas e X) (h : X ≃ₜ X') (Φ : Fin e → LocPot X') (g : X' → ℝ), (∀ i, IsPotential (tAtlas A h) (Φ i)) → Continuous g → mInt (tAtlas A h) Φ g = mInt A (fun i => (Φ i).pullback h h.continuous) (g ∘ h) := by
  first | exact @MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas | exact MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas | (intros; apply MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas <;> assumption)

end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl


theorem _root_.GlobalTheory.T.doubledSpaceFrame_colBlocks_eq : ∀ (α β : Type) [Fintype β] (P Q R S : ℕ) (A : Matrix α (Ix P Q) ℂ) (C : Matrix β (Ix R S) ℂ)
    (c : Matrix (Ix P Q) (Ix (R + S) (S + R)) ℂ),
    (A * c * (dblM C)ᵀ).toCols₁ =
        A * c.submatrix id (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) * Cᵀ ∧
    (A * c * (dblM C)ᵀ).toCols₂ =
        A * c.submatrix id (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) * Cᵀ ∧
    (Jm P Q * c * Jm (R + S) (S + R)).submatrix id
        (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) =
      Jm P Q * c.submatrix id (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) *
        Jm R S ∧
    (Jm P Q * c * Jm (R + S) (S + R)).submatrix id
        (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) =
      -(Jm P Q * c.submatrix id (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) *
        Jm R S) := by
  first | exact @GlobalTheory.RealLift.Dbl.dblM_colBlocks | exact GlobalTheory.RealLift.Dbl.dblM_colBlocks | (intros; apply GlobalTheory.RealLift.Dbl.dblM_colBlocks <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.torusTangentCombination_characterValues : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (H : Over (Sp R)) [GrpObj H] [IsCommMonObj H] (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ → ∀ (r : ℕ) (a : Fin r → D.X → R) (x : Fin r → (epsR R ⟶ H)), (∀ l, (Φ _ (x l)).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (x l)).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (a l χ)))) → ∀ d : Fin r → R, (Φ _ (tanComb d x)).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (tanComb d x)).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (∑ l, d l * a l χ))) := by
  first | exact @GlobalTheory.MBLow.TorusVals.tanComb_vals | exact GlobalTheory.MBLow.TorusVals.tanComb_vals | (intros; apply GlobalTheory.MBLow.TorusVals.tanComb_vals <;> assumption)
end
