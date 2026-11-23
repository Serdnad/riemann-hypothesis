module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1508
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle227
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaTildeHeckeCharSplitMulSignOfNormFormula
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle893
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle065
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1879
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPureTensorAtOriginEqThetaSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle308
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain

@[expose] public section

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.HSShortRun

open GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.HSCore

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem antitone_of_gapGe {g : ℤ} (hg : 0 ≤ g) {la : AllWt.Weight Dw} (h : GapGe g la) (τ : Psi H) : Antitone (la τ) := by
  intro a i hai
  have h0 : ∀ k, 0 ≤ gap (la τ) k := fun k => by
    by_cases hk : k + 1 < Dw.p + Dw.q
    · exact hg.trans (h τ k hk)
    · rw [gap, dite_eq_right hk]
  have e := ofGaps_gap (la τ) a i
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := gap (la τ)) (Finset.range_mono (show (a : ℕ) ≤ i from hai))
    fun k _ _ => h0 k
  rw [ofGaps] at e
  linarith

theorem gapGe_wt_of_wtBig {P : WtPar Dw} (h : WtBig P) : ∀ i, GapGe (FlagTan.dimFlag Dw + 1) (P.wt i) := by
  have h₁ : GapGe (FlagTan.dimFlag Dw + 3) P.u₁ := h.gaps.mono (by
    push_cast
    exact le_mul_of_one_le_right (by positivity) (by omega))
  intro i τ k hk
  have a := h₁ τ k hk
  have b := (P.gap_rem τ k).1
  have c : -2 ≤ gap (FlagTan.kap Dw τ) k := by rw [gap_kap τ hk]; split_ifs <;> omega
  have d : 0 ≤ gap (P.u₁ τ) k := le_trans (by positivity) a
  simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.smul_apply, gap_add, gap_nsmul]
  nlinarith [mul_nonneg (Int.natCast_nonneg i) d, mul_nonneg (Int.natCast_nonneg (FlagTan.dimFlag Dw)) d]

end Weights

variable {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j}


end GlobalTheory.HSShortRun
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.AbVar

variable {K : Type} [Field K] (L : Type) [Field L] [Algebra K L]

def bcAdd (A : AbVar K) : End A →+ End (baseChange L A) where
  toFun f := End.of (bcMap L f.asHom)
  map_zero' := by
    apply End.ext
    change bcMap L (0 : A ⟶ A) = 0
    have h := bcMap_add L (0 : A ⟶ A) 0
    rw [zero_add] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  map_add' f g := End.ext (bcMap_add L f.asHom g.asHom)

theorem bcMap_intCast_sub (A : AbVar K) (n : ℤ) (f : End A) :
    End.of (bcMap L ((n : End A) - f).asHom) =
      (n : End (baseChange L A)) - End.of (bcMap L f.asHom) := by
  have h1 : bcAdd L A 1 = 1 := End.ext (bcMap_id L A)
  have hn : bcAdd L A (n : End A) = (n : End (baseChange L A)) := by
    simp only [← zsmul_one, map_zsmul, h1]
  change bcAdd L A ((n : End A) - f) = (n : End (baseChange L A)) - bcAdd L A f
  rw [map_sub, hn]

theorem isCharpoly_bcMap_iff (A : AbVar K) (f : End A) (P : Polynomial ℤ) :
    IsCharpoly (End.of (bcMap L f.asHom)) P ↔ IsCharpoly f P := by
  unfold IsCharpoly
  have hd : (baseChange L A).dim = A.dim := rfl
  refine and_congr Iff.rfl (and_congr (by rw [hd]) (forall_congr' fun n => ?_))
  rw [← bcMap_intCast_sub, (isIsogeny_bcMap_iff_and_deg_bcMap K L A A _).2]

theorem isCharpoly_unique {A : AbVar K} (f : End A) {P Q : Polynomial ℤ}
    (hP : IsCharpoly f P) (hQ : IsCharpoly f Q) : P = Q :=
  Polynomial.funext fun n => by rw [hP.2.2 n, hQ.2.2 n]

theorem charpoly_bcMap : ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A : AbVar K) (f : End A),
    charpoly (End.of (bcMap L f.asHom)) = charpoly f := by
  intro K _ L _ _ A f
  classical
  unfold charpoly
  by_cases h : ∃ P, IsCharpoly f P
  · have h' : ∃ P, IsCharpoly (End.of (bcMap L f.asHom)) P :=
      let ⟨P, hP⟩ := h; ⟨P, (isCharpoly_bcMap_iff L A f P).2 hP⟩
    rw [dite_eq_left h, dite_eq_left h']
    exact isCharpoly_unique f ((isCharpoly_bcMap_iff L A f _).1 h'.choose_spec) h.choose_spec
  · have h' : ¬ ∃ P, IsCharpoly (End.of (bcMap L f.asHom)) P :=
      fun ⟨P, hP⟩ => h ⟨P, (isCharpoly_bcMap_iff L A f P).1 hP⟩
    rw [dite_eq_right h, dite_eq_right h']

end GlobalTheory.AV.AbVar

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair


open GlobalTheory.DiagLoc in
theorem localRing_graph_of_injective : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  Function.Injective π → (∀ g : K, ∃ a b : R, (b : K) ≠ 0 ∧ g * b = a) →
  IsLocModel (algebraMap ℂ K) R → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → 1 ≤ k →
  ∃ (Q : Subring L) (hQ : IsLocModel (algebraMap ℂ L) Q), letI := hQ.isLocalRing; ∃ z : Fin k → Q,
    IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) ∧ ringKrullDim Q = k ∧
    (∀ g : K, g ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1)) ∧
    (∀ b : κ', b ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      ∃ q : Q, IsUnit q ∧ (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) ∧
    (∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
      ∃ q : Q, (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ∧ q ∈ IsLocalRing.maximalIdeal Q ^ M) ∧
    ∃ (y : Fin (k' + n) → Q) (q : Q), IsFreeGen Q (dForm ((algebraMap ℂ L).codRestrict Q hQ.const_mem) y) ∧ IsUnit q ∧
      dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) = (q : L) • dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  intro K κ κ' L _ _ _ _ _ _ _ _ _ _ _ n k k' x τ' R π ρ hx hτ' hz hπc hπf hπi hRf hR hκ' hk
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_algEquiv_fractionField_of_localRingOfVarietyPoint R π hR hπc hπf hπi
  obtain ⟨z, hz⟩ := hz
  obtain rfl : n = k := GlobalTheory.T.card_transcendenceBasisOverConst_eq_of_algEquiv e n k x z hx hz
  have hK : Algebra.EssFiniteType ℂ K := GlobalTheory.T.essFiniteType_of_localRingOfVarietyPoint R hR
  obtain ⟨O', hO'⟩ := hκ'
  have hκ'f : Algebra.EssFiniteType ℂ κ' := GlobalTheory.T.essFiniteType_of_localRingOfVarietyPoint O' hO'
  set σ : K →ₐ[ℂ] κ' := ρ.comp e.toAlgHom with hσ
  have hQ : IsLocModel (algebraMap ℂ L) (loc L σ) := GlobalTheory.T.isLocalRingOfVarietyPoint_tensorGraphLocalization σ hK hκ'f
  obtain ⟨hm, hdim⟩ := GlobalTheory.T.graphLocalRing_regular_params_and_dim (L := L) σ n x hK hκ'f hx
  have hsum : ∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'),
      algebraMap (K ⊗[ℂ] κ') L (∑ i, (a i : K) ⊗ₜ[ℂ] b i) =
        ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i) := fun l a b => map_sum _ _ _
  have hprod : ∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'),
      Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ') (∑ i, (a i : K) ⊗ₜ[ℂ] b i) =
        ∑ i, ρ (π (a i)) * b i := by
    intro l a b

    simp [map_sum, σ, he]
  refine ⟨loc L σ, hQ, fun i => toLoc L σ (x i ⊗ₜ[ℂ] 1 - 1 ⊗ₜ[ℂ] σ (x i)), hm, hdim, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    refine ⟨toLoc L σ (g ⊗ₜ 1), ?_, rfl⟩
    refine IsUnit.map _ ?_
    exact ((IsUnit.mk0 g hg).map (Algebra.TensorProduct.includeLeft (R := ℂ) (S := ℂ) (B := κ')))
  · intro b hb
    refine ⟨toLoc L σ (1 ⊗ₜ b), ?_, rfl⟩
    refine IsUnit.map _ ?_
    exact ((IsUnit.mk0 b hb).map (Algebra.TensorProduct.includeRight (R := ℂ) (A := K)))
  · intro l a b hne
    refine ⟨toLoc L σ (∑ i, (a i : K) ⊗ₜ[ℂ] b i), ?_, ?_⟩
    · have hs : (∑ i, (a i : K) ⊗ₜ[ℂ] b i) ∈ (ker σ).primeCompl := by
        intro hmem
        exact hne ((hprod l a b).symm.trans hmem)
      exact IsLocalization.map_units (loc L σ) (⟨_, hs⟩ : (ker σ).primeCompl)
    · simp only [coe_toLoc]
      exact hsum l a b
  · intro M l a b hJ
    refine ⟨toLoc L σ (∑ i, (a i : K) ⊗ₜ[ℂ] b i), by simp only [coe_toLoc]; exact hsum l a b, ?_⟩
    let E : K ⊗[ℂ] κ' ≃ₐ[ℂ] κ ⊗[ℂ] κ' := Algebra.TensorProduct.congr e AlgEquiv.refl
    have hE : (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')).comp E.toAlgHom =
        Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ') := by
      apply Algebra.TensorProduct.ext'
      intro g b
      simp [E, σ]
    have hker : ker σ = (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))).comap
        (E : K ⊗[ℂ] κ' →+* κ ⊗[ℂ] κ') := by
      ext s
      simp only [mem_ker, Ideal.mem_comap, RingHom.mem_ker]
      rw [← hE]
      rfl
    have hEs : E (∑ i, (a i : K) ⊗ₜ[ℂ] b i) = ∑ i, π (a i) ⊗ₜ[ℂ] b i := by
      simp [E, he]
    have hmem : (∑ i, (a i : K) ⊗ₜ[ℂ] b i) ∈ ker σ ^ M := by
      have h1 : (∑ i, (a i : K) ⊗ₜ[ℂ] b i) = E.symm (∑ i, π (a i) ⊗ₜ[ℂ] b i) := by
        rw [← hEs, AlgEquiv.symm_apply_apply]
      have h2 := Ideal.mem_map_of_mem (E.symm : κ ⊗[ℂ] κ' →+* K ⊗[ℂ] κ') hJ
      have h3 : (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))).comap
          (E : K ⊗[ℂ] κ' →+* κ ⊗[ℂ] κ') =
          (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))).map
          (E.symm : κ ⊗[ℂ] κ' →+* K ⊗[ℂ] κ') := by
        ext s
        rw [Ideal.mem_comap, Ideal.mem_map_iff_of_surjective (E.symm : κ ⊗[ℂ] κ' →+* K ⊗[ℂ] κ')
          E.symm.surjective]
        constructor
        · intro hs
          exact ⟨E s, hs, by simp⟩
        · rintro ⟨t, ht, rfl⟩
          simpa using ht
      rw [h1, hker, h3, ← Ideal.map_pow]
      exact h2
    have := Ideal.mem_map_of_mem (toLoc L σ) hmem
    rw [Ideal.map_pow, map_ker] at this
    exact this
  · refine ⟨_, 1, GlobalTheory.T.topForms_graphLocalRing_freelyGenerated σ n k' x τ' hQ.const_mem hK hκ'f hx hτ', isUnit_one, ?_⟩
    rw [Submonoid.coe_one, one_smul]
    congr 1
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

end GlobalTheory.FieldPair
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RouteSeesaw

theorem isThetaFunO_of_isMatched : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
    ∀ d ∈ Θ.support, IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) d.2 := by
  intro D T L sc G μ₀ _hL W B ρ t i j Θ Θ' hM d hd
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, hF, rfl, -⟩ := hM
  obtain ⟨e, -, -, φ₁, φ₂, hφ, -⟩ := hF
  unfold tensT at hd
  obtain ⟨P, -, hd⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  obtain ⟨d', hd', hd⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  have hd := Finsupp.support_single_subset hd
  rw [Finset.mem_singleton] at hd
  subst hd
  obtain ⟨h₁, h₂⟩ := hφ d' hd'
  have v₁ := (ρ.vX_is i (j + 1) i.2 j.2).2.2
  have v₂ := (ρ.vT_is t (i + 1) j i.2 j.2).2.2
  exact ⟨GlobalTheory.FockTheta.ptStable D _ _ W.ψ_std W.θ_is _ _ _ _ _ _ _ _
      (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h₁.2 v₁),
    GlobalTheory.FockTheta.ptStable D _ _ W.ψ_std W.θ_is _ _ _ _ _ _ _ _
      (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h₂.2 v₂)⟩

end GlobalTheory.RouteSeesaw
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum

theorem conj_smul_ne_of_isIdemAt {D : D7} {e : Formalism.L2.Theta.AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt e P) : D.host.conj • P.asIdeal ≠ P.asIdeal := by
  intro h
  have hc := GlobalTheory.EtaProduct.cA_of_fixed (GlobalTheory.HeckeDetChar.isPlIdem he) h
  have h0 : e = 0 := by
    have := he.1.2.1
    rw [hc, he.1.1] at this
    exact this
  apply P.ne_bot
  refine eq_bot_iff.2 fun x hx => ?_
  by_contra hx0
  have := (he.2 x hx0).1 hx
  rw [h0, zero_mul, map_zero] at this
  exact this (zero_mem _)

theorem condE_isCoprime_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L),
    IsCoprime (condE P) (D.host.conj • condE P) := by
  intro D T L P
  have hF : ∀ I : Ideal (𝓞 D.host.E), (D.host.conj • I).under (𝓞 D.host.F) = I.under (𝓞 D.host.F) :=
    GlobalTheory.PlaceOverPair.under_smul_of_fix D.host.conj
      (fun x => (D.host.conjE_mem_hostF_iff _).1 x.2)
  unfold GlobalTheory.FunObj.SqNum.condE
  rw [Finset.smul_prod']
  refine IsCoprime.prod_left fun v hv => IsCoprime.prod_right fun v' hv' => ?_
  rw [smul_pow']
  refine IsCoprime.pow ?_
  rw [Ideal.isCoprime_iff_sup_eq]
  have hm : (D.host.conj • (P.w v').asIdeal).IsMaximal := by
    have := (P.w v').isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => (P.w v').ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  refine Ideal.IsMaximal.coprime_of_ne (P.w v).isMaximal hm fun heq => ?_
  have hvv : v = v' := by
    have a := congrArg HeightOneSpectrum.asIdeal (P.under_w hv)
    have b := congrArg HeightOneSpectrum.asIdeal (P.under_w hv')
    refine HeightOneSpectrum.ext ?_
    rw [← a, ← b]
    show Ideal.under _ _ = Ideal.under _ _
    rw [heq, hF]
  subst hvv
  obtain ⟨e, he⟩ := P.w_split v hv
  exact conj_smul_ne_of_isIdemAt he heq.symm

end GlobalTheory.FunObj.StdDatum

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj.TopJet

open Formalism.MainNotions.TaylorLogMetric in
theorem applyAt0_monomial (D : D7) {N N' : ℕ} (k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ) (G : VC D N N' → ℂ) :
    Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G = (k.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G k := by
  classical
  unfold Formalism.MainNotions.GL3Theta.applyAt0
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl,
    one_mul]

open Formalism.MainNotions.TaylorLogMetric in
theorem taylor_comp_smul (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ) (hG : Differentiable ℂ G) (a : ℂ) (α : Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun z => G (a • z)) α = a ^ (α.sum fun _ n => n) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  unfold Formalism.MainNotions.TaylorLogMetric.taylor
  have key := iteratedFDeriv_comp_const_smul (𝕜 := ℂ) (i := Multiset.card (Finsupp.toMultiset α)) (f := G) a ((ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_diff hG).of_le (by exact_mod_cast le_top))
  rw [key]
  simp only [smul_zero, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]
  congr 2
  exact Finsupp.card_toMultiset α

open Formalism.MainNotions.TaylorLogMetric in
theorem taylor_const_smul (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ) (hG : Differentiable ℂ G) (c : ℂ) (α : Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (c • G) α = c * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  unfold Formalism.MainNotions.TaylorLogMetric.taylor
  have key := iteratedFDeriv_const_smul_apply (𝕜 := ℂ) (i := Multiset.card (Finsupp.toMultiset α)) (f := G) (x := 0) (a := c) (((ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_diff hG).of_le (by exact_mod_cast le_top)).contDiffAt)
  rw [key, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    mul_div_assoc]

theorem fockIn_vacuum_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.top t j)).rank (G.pT (.top t j)).rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ c : ℂˣ, ∀ k : FVar D (G.pT (.top t j)).rank (G.pS (.top t j)).rank →₀ ℕ, GlobalTheory.FunObj.fockIn W N.frC (.top t j) f (MvPolynomial.monomial k 1) 0 = c * ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0) := by
  intro D T L sc G W U N δ t0 hC hδ hT t j hj e0 he0 f hf
  obtain ⟨θ, hθTh, hθ0, hreal⟩ := GlobalTheory.T.vacuum_real_restriction_gaussian_mul_theta W N δ hC hδ t j hj f hf
  have hG1 := (GlobalTheory.InducedType.induced_type D).1
  have he0ne : e0 ≠ 0 := by
    intro h
    have h1 := he0.2.2.1
    rw [h] at h1
    simp only [Formalism.MainNotions.TaylorLogMetric.normSq, Pi.zero_apply, norm_zero] at h1
    have h2 := h1.symm
    simp at h2
    exact GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D hG1 _ δ t0 hC hT h2.1
  obtain ⟨c, hc⟩ := (GlobalTheory.ThetaLine.theta_line D hG1 _ δ hC _ _ _
    (Or.inr ⟨_, _, GlobalTheory.FinWeil.Vacuum.sd_std D _, GlobalTheory.FinWeil.Vacuum.sd_std D _, rfl⟩)).1 θ hθTh e0 he0.1 he0ne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hθ0 (by rw [hc, zero_smul])
  refine ⟨Units.mk0 c hc0, fun k => ?_⟩
  have hdiff : Differentiable ℂ (fun z => θ (δ • z)) := hθTh.1.comp (differentiable_id.const_smul δ)
  rw [GlobalTheory.T.fockJet_gaussianEntire_origin_gridFrames W N t j hj f (fun z => θ (δ • z)) hdiff hreal k, applyAt0_monomial, applyAt0_monomial,
    taylor_comp_smul D θ hθTh.1, hc, taylor_const_smul D e0 he0.1.1]
  have hper : ∀ τ : D.what₂.Tau, GlobalTheory.FunObj.period δ τ = δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) := by
    intro τ
    rw [GlobalTheory.FunObj.period, GlobalTheory.AdTh.Fock.norm_embedding_hostFormConstant_eq, div_eq_mul_inv]
  have hprod : (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) =
      (δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹)) ^ (k.sum fun _ n => n) := by
    simp only [hper, Finsupp.prod, Finsupp.sum]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  rw [hprod, Units.val_mk0, mul_pow]
  ring

end GlobalTheory.FunObj.TopJet
end
