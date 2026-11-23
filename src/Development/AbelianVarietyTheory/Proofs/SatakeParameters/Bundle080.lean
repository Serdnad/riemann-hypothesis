module

public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SatakeDualWeyl.Bundle001
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Unramified.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle067
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle055
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle070
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle057
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle047
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle164
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle281
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle218
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle053
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle012
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle298
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle073
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle074
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN

@[expose] public section

section

open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix

namespace GlobalTheory.InertConj

theorem conj_mem_of_inert {E : Type} [Field E] [NumberField E] [IsCMField E]
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))} {P : HeightOneSpectrum (𝓞 E)}
    (h : IsInertAt (maximalRealSubfield E) E v P) {x : 𝓞 E} (hx : x ∈ P.asIdeal) :
    IsCMField.ringOfIntegersComplexConj E x ∈ P.asIdeal := by
  have h' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = P.asIdeal := h
  have key : P.asIdeal ≤ Ideal.comap
      (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E) P.asIdeal := by
    conv_lhs => rw [← h']
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change IsCMField.ringOfIntegersComplexConj E _ ∈ _
    rw [AlgEquiv.commutes, ← h']
    exact Ideal.mem_map_of_mem _ hs
  exact key hx

theorem exists_conj_completion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E)), IsInertAt (maximalRealSubfield E) E v P → ∃ (σ : P.adicCompletion E →+* P.adicCompletion E) (ϖ : P.adicCompletion E), (∀ x : E, σ (algebraMap E (P.adicCompletion E) x) = algebraMap E (P.adicCompletion E) (ReciprocityTheory.ChartRestriction.G.FD.cc x)) ∧ (∀ x, σ (σ x) = x) ∧ (∀ x, Valued.v (σ x) = Valued.v x) ∧ (∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) ∧ σ ϖ = ϖ ∧ IsUnifV E P ϖ := by
  intro E _ _ _ _ v P h
  have h' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = P.asIdeal := h
  have hc : Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv P P := by
    rw [Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    have e : y = IsCMField.ringOfIntegersComplexConj E x := RingOfIntegers.ext hxy
    rw [e]
    refine ⟨conj_mem_of_inert h, fun hx => ?_⟩
    have h2 := conj_mem_of_inert h hx
    have e2 : IsCMField.ringOfIntegersComplexConj E (IsCMField.ringOfIntegersComplexConj E x) = x := by
      ext; simp
    rwa [e2] at h2
  obtain ⟨σ, σ1, σ2, σ3⟩ := UnramCompletion.exists_ringEquiv P _ hc
  have σ2' : ∀ x : E, σ (algebraMap E (P.adicCompletion E) x) =
      algebraMap E (P.adicCompletion E) (ReciprocityTheory.ChartRestriction.G.FD.cc x) := σ2
  obtain ⟨s, hs, hs2⟩ : ∃ s ∈ v.asIdeal,
      algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s ∉ P.asIdeal ^ 2 := by
    by_contra hn
    push Not at hn
    have h1 : P.asIdeal ≤ P.asIdeal ^ 2 := by
      conv_lhs => rw [← h']
      exact Ideal.map_le_iff_le_comap.2 hn
    exact (Ideal.pow_lt_self _ P.ne_bot P.isPrime.ne_top 2 le_rfl).not_ge h1
  have hs1 : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s ∈ P.asIdeal :=
    h' ▸ Ideal.mem_map_of_mem _ hs
  have hval : ∀ a : 𝓞 E, Valued.v (algebraMap E (P.adicCompletion E) (a : E)) =
      P.valuation E (algebraMap (𝓞 E) E a) := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _
  refine ⟨σ, algebraMap E _ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E), σ2', ?_, σ3,
    ?_, ?_, ?_⟩
  · intro x
    refine congrFun (UnramCompletion.ringHom_ext_of_continuous P (f := fun x => σ (σ x))
      (σ1.comp σ1) continuous_id fun k => ?_) x
    simp [σ2', ReciprocityTheory.ChartRestriction.G.FD.cc]
  · obtain ⟨x, hx⟩ := exists_sub_conj_notMem P.asIdeal P.isPrime.ne_top
    refine ⟨algebraMap E _ (x : E), ?_, ?_⟩
    · rw [hval]; exact P.valuation_le_one x
    · change Valued.v (σ _ - _) = 1
      rw [Valuation.map_sub_swap, σ2', ← map_sub]
      exact (hval (x - IsCMField.ringOfIntegersComplexConj E x)).trans
        ((HeightOneSpectrum.valuation_eq_one_iff_notMem P).2 hx)
  · change σ _ = _
    rw [σ2', cc_algebraMap]
  · unfold IsUnifV
    rw [hval, HeightOneSpectrum.valuation_of_algebraMap]
    exact UnramCompletion.intValuation_eq_of_notMem_sq P hs1 hs2

end GlobalTheory.InertConj
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.Host GlobalTheory.KerJ NumberField Classical

theorem _root_.GlobalTheory.T.rhoThreeOf_of_determinantCharacterFiniteOrderType : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ), MtType u mt → rhoThreeOf D C mt := by
  first | exact @GlobalTheory.KerJ.RhoThree.rhoThreeOf_of_mtType | exact GlobalTheory.KerJ.RhoThree.rhoThreeOf_of_mtType | (intros; apply GlobalTheory.KerJ.RhoThree.rhoThreeOf_of_mtType <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.OnePlace

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem GlobalTheory.TwU

def xiE {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]) :
    Eidx n' r0 r1 ⊕ Eidx n' r0 r1 → MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p]
  | Sum.inl (r, a, b) => MvPowerSeries.subst (fun s : ZMod n' =>
      (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) (x (Sum.inl r))
  | Sum.inr (r, a, b) => MvPowerSeries.subst (fun s : ZMod n' =>
      (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) (x (Sum.inr r))

def jetZ (p : ℕ) [Fact p.Prime] (n' r0 r1 : ℕ) (z : Zidx n' r0 r1) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p] :=
  jetLogG p n' (((z.1 : ℕ) : ZMod n'), z.2)

end GlobalTheory.OnePlace

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.TwU

theorem std_at_served : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D), LatTied hT X Y → 2 * rG L.sc ≤ D.R.k → ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (D.gat u w hg).P.m (Y.Fl u w hg).t (Y.Fl u w hg).mm (Y.Fl u w hg).c (D.gat u w hg).P.r ((Y.Fl u w hg).TT v) ((Y.Fl u w hg).a v) ((Y.Fl u w hg).b v) ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) := by
  intro D u w hg L hT X Y hLT hk v
  obtain ⟨hmm, -, -, hr, -⟩ := hLT u w hg
  have hS := (D.gat u w hg).P.setting v
  have hgk := hT.gat_k u w hg
  have hrG : 1 ≤ rG L.sc := Nat.succ_le_succ (Nat.zero_le _)
  have hm2 := D.R.two_le_m
  refine ⟨hg.1, hg.2.1, hS.two_le, hS.even, ?_, ?_, ?_, (Y.Fl u w hg).base v, (D.gat u w hg).P.dom v, ?_, ?_⟩
  · rw [hr]; split_ifs <;> omega
  · rw [hr, hgk]; split_ifs <;> omega
  · rw [hmm]; omega
  · exact fun s => ⟨le_trans (le_max_left _ _) ((Y.Fl u w hg).w_ge v s),
      le_trans (le_max_right _ _) ((Y.Fl u w hg).w_ge v s)⟩
  · exact fun s l hl _ => (Y.Fl u w hg).w_mono v s l hl

end GlobalTheory.TwU
end

section

noncomputable section

namespace GlobalTheory.TwU

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem inParam_eq_subst_log (p : ℕ) [Fact p.Prime] {ι : Type} (f : MvPowerSeries ι (K0 p)) :
    inParam p f = MvPowerSeries.subst (Formalism.MainNotions.FormalGroupSystem.Pf.en_aL p (K0 p)) f := by
  have h : Formalism.MainNotions.FormalGroupSystem.Pf.en_L p (K0 p) = logF p := by
    ext k; simp [Formalism.MainNotions.FormalGroupSystem.Pf.en_L]
  unfold inParam Formalism.MainNotions.FormalGroupSystem.Pf.en_aL
  rw [h]

theorem monomial_param_as_log_series : ∀ (p : ℕ) [Fact p.Prime] (ι : Type) [Fintype ι] (n : ι →₀ ℕ),
    ∃ U : MvPowerSeries ι (K0 p), inParam p U = MvPowerSeries.monomial n 1 ∧
      (∀ m : ι →₀ ℕ, m.degree < n.degree → MvPowerSeries.coeff m U = 0) := by
  intro p _ ι _ n
  have hs := Formalism.MainNotions.FormalGroupSystem.Pf.en_Ec_hs p (K0 p) (ι := ι)
  have hl := Formalism.MainNotions.FormalGroupSystem.Pf.en_aL_hs p (K0 p) (ι := ι)
  refine ⟨MvPowerSeries.subst (Formalism.MainNotions.FormalGroupSystem.Pf.en_Ec p (K0 p)) (MvPowerSeries.monomial n (1 : K0 p)), ?_, ?_⟩
  · rw [inParam_eq_subst_log, MvPowerSeries.subst_comp_subst_apply hs hl]
    simp only [Formalism.MainNotions.FormalGroupSystem.Pf.en_aL_Ec]
    rw [MvPowerSeries.subst_self]
    rfl
  · intro m hm
    apply MvPowerSeries.coeff_of_lt_order
    refine lt_of_lt_of_le (Nat.cast_lt.mpr hm) ?_
    rw [MvPowerSeries.subst_monomial hs, map_one, one_mul, Finsupp.prod]
    refine le_trans ?_ (MvPowerSeries.le_order_prod _ _)
    have hd : n.degree = ∑ i ∈ n.support, n i := rfl
    rw [hd, Nat.cast_sum]
    exact Finset.sum_le_sum fun s _ =>
      MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (Formalism.MainNotions.FormalGroupSystem.Pf.en_Ec_zero p (K0 p) s)

end GlobalTheory.TwU

end
end

section

open Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.SplitField

theorem exists_finite_ext_absIrrSub : ∀ {K Γ ι : Type} [Field K] [Group Γ] [Finite ι] {a : ℕ} (ρ : ι → (Γ →* GL (Fin a) K)), (∀ j, IsSSRep (mapRep (algebraMap K (AlgebraicClosure K)) (ρ j))) → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K'), ∀ j W, IsIrrSub (mapRep (algebraMap K K') (ρ j)) W → AbsIrrSub (mapRep (algebraMap K K') (ρ j)) W := by
  intro K Γ ι _ _ _ a ρ hss
  classical
  have hdec := fun j => GlobalTheory.semisimple_matrix_rep_decomp (mapRep (algebraMap K (AlgebraicClosure K)) (ρ j)) (hss j)
  choose n Vs hint hirr using hdec
  let b : ∀ j m, Module.Basis (Fin (Module.finrank (AlgebraicClosure K) (Vs j m))) (AlgebraicClosure K) (Vs j m) :=
    fun j m => Module.finBasis (AlgebraicClosure K) (Vs j m)
  let S : Set (AlgebraicClosure K) := Set.range (fun p : (Σ j, Σ m : Fin (n j), Fin (Module.finrank (AlgebraicClosure K) (Vs j m)) × Fin a) =>
    ((b p.1 p.2.1 p.2.2.1 : Vs p.1 p.2.1) : Fin a → AlgebraicClosure K) p.2.2.2)
  obtain ⟨K', _, _, _, f, hf, hS⟩ := exists_finite_field S (Set.finite_range _)
  refine ⟨K', inferInstance, inferInstance, inferInstance, ?_⟩
  intro j
  set τ := mapRep (algebraMap K K') (ρ j) with hτ
  have hcomp : mapRep f τ = mapRep (algebraMap K (AlgebraicClosure K)) (ρ j) := by
    rw [hτ, mapRep_mapRep]
    congr 1
    exact RingHom.ext hf
  have hsp : ∀ m, Vs j m ≤ Submodule.span (AlgebraicClosure K) ((fun v => f ∘ v) '' {v : Fin a → K' | f ∘ v ∈ Vs j m}) := by
    intro m
    have h1 : Vs j m = Submodule.span _ (Set.range fun k => ((b j m k : Vs j m) : Fin a → AlgebraicClosure K)) := by
      have := congrArg (Submodule.map (Vs j m).subtype) (b j m).span_eq
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at this
      refine this.symm.trans ?_
      rw [← Set.range_comp]; rfl
    conv_lhs => rw [h1]
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have hc : ∀ i, ∃ c : K', f c = ((b j m k : Vs j m) : Fin a → AlgebraicClosure K) i :=
      fun i => hS ⟨⟨j, m, k, i⟩, rfl⟩
    choose c hc using hc
    have hfc : f ∘ c = ((b j m k : Vs j m) : Fin a → AlgebraicClosure K) := funext hc
    refine Submodule.subset_span ⟨c, ?_, ?_⟩
    · show f ∘ c ∈ Vs j m
      rw [hfc]; exact (b j m k).2
    · exact hfc
  obtain ⟨Us, hUi, hUs⟩ := GlobalTheory.T.exists_internal_stable_decomposition_descends_to_subfield f τ (Vs j) (hint j) (fun m => hcomp ▸ (hirr j m).2.1) hsp
  have hES : ∀ m, EndSpanned τ (Us m) := by
    intro m
    apply GlobalTheory.T.endSpannedByRepMatrices_of_scalarExtension f τ (Us m)
    rw [(hUs m).2, hcomp]
    exact GlobalTheory.T.endSpanned_of_isIrrSub_of_isAlgClosed' _ _ (hirr j m)
  have hne : ∀ m, Us m ≠ ⊥ := by
    intro m h
    apply (hirr j m).1
    rw [← (hUs m).2, h]
    simp
  have hUirr : ∀ m, IsIrrSub τ (Us m) := fun m => isIrrSub_of_endSpanned τ (Us m) (hne m) (hUs m).1 (hES m)
  intro W hW
  obtain ⟨m, hm⟩ := GlobalTheory.T.irreducible_subrep_iso_summand_of_isInternal τ Us hUi hUirr W hW
  exact absIrrSub_of_endSpanned τ W hW.1 hW.2.1 (endSpanned_of_isoSub τ W (Us m) hW.2.1 hm (hES m))
end GlobalTheory.SplitField
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.Rec

theorem continuous_cycLL_period : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l),
    Continuous (fun s => ((cycLL (P.PD K) ↥LL.1 s : (↥LL.1)ˣ) : ↥LL.1)) := by
  intro l _ P K LL
  have h := (GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.1
  have e : (fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1)) =
      fun g : ↥(GK K) => algebraMap ℚ_[l] ↥LL.1 (P.χQ (g : GQ l) : ℚ_[l]) := by
    funext g
    change algebraMap ℚ_[l] ↥LL.1 (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = _
    rw [P.PD_χ]
  rw [e]
  refine Continuous.subtype_mk (f := fun g : ↥(GK K) =>
    algebraMap ℚ_[l] (Om l) (P.χQ (g : GQ l) : ℚ_[l])) ?_ _
  exact (continuous_algebraMap ℚ_[l] (Om l)).comp (h.comp continuous_subtype_val)

end GlobalTheory.HTW.Rec
end
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem goodO_finExt_integers :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) :=
  GlobalTheory.Pass.goodO_ringOfIntegers

end GlobalTheory.HTW.Rec
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct :
    ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ}
      (ρ : Γ →* GL (Fin a) k), IsSSRep ρ → (∀ W, IsIrrSub ρ W → AbsIrrSub ρ W) →
      (∀ W₁ W₂, IsIrrSub (mapRep f ρ) W₁ → IsIrrSub (mapRep f ρ) W₂ → W₁ ⊓ W₂ = ⊥ →
        ¬ IsoSub (mapRep f ρ) W₁ W₂) →
      AbsIrrDistinct (matRep ((Units.coeHom _).comp ρ)) := by
  intro k Γ _ _ L _ f a ρ hss habs hdist
  obtain ⟨n, Vs, hint, hirr⟩ := GlobalTheory.T.semisimple_matrixRep_isInternal_irreducible ρ hss
  have hs : ∀ j, Stable (matRep ((Units.coeHom _).comp ρ)) (Vs j) :=
    fun j g v hv => (hirr j).2.1 g v hv
  have hsp : ∀ j, Submodule.span k (Set.range fun g =>
      (matRep ((Units.coeHom _).comp ρ) g).restrict (hs j g)) = ⊤ :=
    fun j => GlobalTheory.T.span_restrict_eq_top_of_absIrrSub_alt ρ (Vs j) (hs j) (habs _ (hirr j))
  refine ⟨Fin n, inferInstance, inferInstance, Vs, hs, hint, fun j => (hirr j).1, hsp, ?_⟩
  intro j j' hjj' e he
  have hiso : IsoSub ρ (Vs j) (Vs j') := by
    refine ⟨e, fun g v h => ?_⟩
    have := congrArg Subtype.val (he g v)
    exact this
  have hdisj : Vs j ⊓ Vs j' = ⊥ :=
    (hint.submodule_iSupIndep.pairwiseDisjoint hjj').eq_bot
  exact hdist _ _
    (GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top f ρ (Vs j) (hs j) (hirr j).1 (hsp j))
    (GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top f ρ (Vs j') (hs j') (hirr j').1 (hsp j'))
    (GlobalTheory.T.span_extendScalars_inf_eq_bot_of_inf_eq_bot f (Vs j) (Vs j') hdisj)
    (GlobalTheory.T.isoSub_span_extension_of_scalars f ρ (Vs j) (Vs j') (hirr j).2.1 (hirr j').2.1 hiso)

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NRows

theorem isHeckeGaloisQ_of_isHeckeGalois : ∀ (D : D7) (i : D.nd.Loc) (x : D.nd.X i)
    (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)),
    IsHeckeGalois D.nd i x r → SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) r) := by
  intro D i x r hr
  refine ⟨SumRepresentations.contQ_of_continuous D.nd D.naut i r hr.1, ?_, ?_⟩
  · have : CharZero (Kf D.nd i) := RingHom.charZero (D.naut.iotaQ i)
    have h := GlobalTheory.TraceSemisimple.isSSRep_mapRep _ _ _ (D.naut.iotaQ i) _ _ hr.2.1
    have e : mapRep (iotaOQ D.nd D.naut i) r =
        mapRep (D.naut.iotaQ i) (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) r) := by
      ext g a b
      rfl
    rw [e]
    exact h
  · intro w hw B σ hB hσ
    have e3 : ((mapRep (iotaOQ D.nd D.naut i) r σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))) =
        ((r σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (iotaOQ D.nd D.naut i) := rfl
    rw [e3, Matrix.charpoly_map, hr.2.2 w hw B σ hB hσ]

end GlobalTheory.NRows
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.orderOf_eq_max_two_of_sign_neg_implicit : ∀ {fr : Formalism.HC.Frame} (φ : fr.GG), φ.1.2 = -1 → orderOf φ = Nat.lcm 2 (orderOf φ.2) := by
  first | exact @GlobalTheory.orderOf_moving_stmt | exact GlobalTheory.orderOf_moving_stmt | (intros; apply GlobalTheory.orderOf_moving_stmt <;> assumption)
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.alternatingWord_large_size_numerical_bounds : ∀ (l : ℕ) (B η S M b : ℝ), 11 ≤ l → 100 ≤ B → 0 ≤ η → 0 ≤ S → 2 * η + S ≤ B / 10 → |M - B| ≤ η → |b - B| ≤ η → (M + S) / 2 ≤ b ∧ 2 * ((M + S + η) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + 3 + (Real.logb l (2 * (M + S + η)) + 1)) + η + 1 ≤ b := by
  first | exact @GlobalTheory.alternatingWord_numerical_bounds | exact GlobalTheory.alternatingWord_numerical_bounds | (intros; apply GlobalTheory.alternatingWord_numerical_bounds <;> assumption)
end
