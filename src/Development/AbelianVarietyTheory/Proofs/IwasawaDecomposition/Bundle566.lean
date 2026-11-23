module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotExistsExponentConditionCard
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCompatibleConjugationRepresentation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LabConj
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPlacesOverOfIsConjPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle478
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle115
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle486
import Formalism.LocalToGlobal.Divisibility.PsiWeilOfAbsNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.GridField

open GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun

def vPre (s : Stages) (v : HeightOneSpectrum (𝓞 s.toD7.host.F)) : HeightOneSpectrum (𝓞 s.B.toPre.host.F) := v

def toPl {P Q : Pre} (h : P = Q) (v : HeightOneSpectrum (𝓞 P.host.F)) : HeightOneSpectrum (𝓞 Q.host.F) := by
  subst h
  exact v

theorem leastSplitAuxiliaryPrime_congr_preData {s s' : Stages} (h : s.B.toPre = s'.B.toPre) : GlobalTheory.ChiGrid.q0 s.toD7 = GlobalTheory.ChiGrid.q0 s'.toD7 := by
  obtain ⟨B, C, W, V, S, N, Gj⟩ := s
  obtain ⟨B', C', W', V', S', N', Gj'⟩ := s'
  cases B
  cases B'
  dsimp only at h
  subst h
  rfl

theorem exists_gridData_pl_eq_and_fieldHas_of_basePlace_eq {s s' : Stages} {B₀ : Pre} (hs : s.B.toPre = B₀) (hs' : s'.B.toPre = B₀) {T T' : Type}
    {L : Formalism.IndefR.Links.LevCh s.toD7 T} {L' : Formalism.IndefR.Links.LevCh s'.toD7 T'} {sc : Consts} (G : GridData L sc)
    (G' : GridData L' sc) (hv : toPl hs' (vPre s' G'.pl.v0) = toPl hs (vPre s G.pl.v0)) {K : Type} [Field K]
    (e : K →+* ℂ) (hF : FieldHas G' e) : ∃ G'' : GridData L sc, G''.pl = G.pl ∧ FieldHas G'' e := by
  subst hs
  obtain ⟨B, C, W, V, S, N, Gj⟩ := s
  obtain ⟨B', C', W', V', S', N', Gj'⟩ := s'
  cases B
  cases B'
  dsimp only at hs'
  subst hs'
  have hv0 : G'.pl.v0 = G.pl.v0 := hv
  refine ⟨⟨G.pl, ⟨G'.ch.chiH, G'.ch.chi, G'.ch.chi_eq, G'.ch.triv, G'.ch.inf,
      fun i h1 h2 PP hPP => G'.ch.unr i h1 h2 PP ?_, G'.ch.lev1, G'.ch.wild,
      fun i h1 h2 PP hPP => G'.ch.lev0 i h1 h2 PP (hPP.trans hv0.symm)⟩, G.sp⟩, rfl, ?_⟩
  · intro h
    apply hPP
    rcases G'.pl.mem_S0_of_sum_eq.1 h with h | h
    · exact G.pl.mem_S0_of_sum_eq.2 (Or.inl (h.trans hv0))
    · exact G.pl.mem_S0_of_sum_eq.2 (Or.inr h)
  · refine ⟨hF.values, fun v hv => ?_⟩
    have hd : G.pl.depth sc v = G'.pl.depth sc v := by
      unfold Places.depth
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (h1.trans hv0.symm) h2
      · exact absurd (h2.trans hv0) h1
      · rfl
    rw [hd]
    refine hF.roots v ?_
    rcases G.pl.mem_S0_of_sum_eq.1 hv with h | h
    · exact G'.pl.mem_S0_of_sum_eq.2 (Or.inl (h.trans hv0.symm))
    · exact G'.pl.mem_S0_of_sum_eq.2 (Or.inr h)

theorem exists_field_uniform : ∀ (cDep b : ℝ) (B₀ : Pre), ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
    ∀ (s : Stages), s.B.toPre = B₀ → 0 < GlobalTheory.ChiGrid.q0 s.toD7 → ∀ (T : Type) (L : Formalism.IndefR.Links.LevCh s.toD7 T)
      (_G : GlobalTheory.ChiGrid.GridData L ⟨1, cDep, b⟩), ∃ G' : GlobalTheory.ChiGrid.GridData L ⟨1, cDep, b⟩,
        GlobalTheory.BigTop.Fun.FieldHas G' M.val.toRingHom := by
  intro cDep b B₀
  classical

  let Wit : Set (HeightOneSpectrum (𝓞 B₀.host.F)) := {v | ∃ (s : Stages) (hs : s.B.toPre = B₀) (T : Type)
    (L : Formalism.IndefR.Links.LevCh s.toD7 T) (G : GridData L ⟨1, cDep, b⟩), toPl hs (vPre s G.pl.v0) = v}
  have hfin : Wit.Finite := by
    rcases Wit.eq_empty_or_nonempty with h | ⟨v₁, s₁, hs₁, T₁, L₁, G₁, -⟩
    · rw [h]
      exact Set.finite_empty
    · have hn : ((GlobalTheory.ChiGrid.q0 s₁.toD7 : ℕ) : 𝓞 B₀.host.F) ≠ 0 := by
        subst hs₁
        exact_mod_cast (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec s₁.toD7).1.ne_zero
      refine (Formalism.L2.DIV.primesOf ((GlobalTheory.ChiGrid.q0 s₁.toD7 : ℕ) : 𝓞 B₀.host.F)).finite_toSet.subset ?_
      rintro _ ⟨s, hs, T, L, G, rfl⟩
      refine Formalism.L2.DIV.mem_primesOf.2 ⟨hn, ?_⟩
      subst hs
      rw [leastSplitAuxiliaryPrime_congr_preData hs₁]
      exact G.pl.basePlace_over_qZero
  have hex : ∀ v : Wit, ∃ Mv : IntermediateField ℚ ℂ, FiniteDimensional ℚ Mv ∧
      ∃ (s : Stages) (hs : s.B.toPre = B₀) (T : Type) (L : Formalism.IndefR.Links.LevCh s.toD7 T)
        (G : GridData L ⟨1, cDep, b⟩), toPl hs (vPre s G.pl.v0) = v ∧ FieldHas G Mv.val.toRingHom := by
    rintro ⟨v, s, hs, T, L, G, hv⟩
    obtain ⟨Mv, h1, h2⟩ := exists_fieldHas G
    exact ⟨Mv, h1, s, hs, T, L, G, hv, h2⟩
  choose Mv hMv hW using hex
  haveI := hfin.to_subtype
  haveI : ∀ v, FiniteDimensional ℚ (Mv v) := hMv
  refine ⟨⨆ v, Mv v, IntermediateField.finiteDimensional_iSup_of_finite, ?_⟩
  intro s hs _ T L G
  obtain ⟨s', hs', T', L', G', hv', hF⟩ := hW ⟨toPl hs (vPre s G.pl.v0), s, hs, T, L, G, rfl⟩
  have hF' : FieldHas G' (⨆ v, Mv v).val.toRingHom :=
    FieldHas.map (IntermediateField.inclusion (le_iSup Mv _)).toRingHom hF
  obtain ⟨G'', -, h⟩ := exists_gridData_pl_eq_and_fieldHas_of_basePlace_eq hs hs' G G' hv' _ hF'
  exact ⟨G'', h⟩

end GlobalTheory.GridField

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridLambdaData

theorem isAuxiliaryHeckeCharacter_toricListOfGrid : ∀ (D : D7) {T : Type} (L : Formalism.IndefR.Links.LevCh D T) (sc : GlobalTheory.ChiGrid.Consts) (G : GlobalTheory.ChiGrid.GridData L sc) (w0 : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.LamTie.PlacesOk D.host (AbsolutelyIrreducibleSpan.q0 D) w0 → ∀ a : Fin D.R.m, GlobalTheory.LamTie.IsAuxiliaryHeckeCharacter D.host (G.pl.w G.pl.v0) ((GlobalTheory.BigTop.Fun.lamOf G).c a) ((GlobalTheory.BigTop.Fun.lamOf G).chi a) := by
  intro D T L sc G _ _ a
  have hw0 : (G.pl.w G.pl.v0).under (𝓞 D.host.F) = G.pl.v0 := G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
  have hS1 : ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.LamTie.Over4 D.host w → w.under (𝓞 D.host.F) ∈ GlobalTheory.ChiGrid.S1 D := by
    intro w h
    rw [GlobalTheory.ChiGrid.S1_mem_OmF]
    rcases h with ⟨k, hk⟩ | hk | hk
    · fin_cases k
      · exact Or.inl (GlobalTheory.BigTop.Fun.natCast_mem_under hk)
      · exact Or.inr (Or.inl (GlobalTheory.BigTop.Fun.natCast_mem_under hk))
    · exact Or.inr (Or.inr (Or.inl (GlobalTheory.BigTop.Fun.natCast_mem_under hk)))
    · exact Or.inr (Or.inr (Or.inr (GlobalTheory.BigTop.Fun.natCast_mem_under hk)))
  have hOv : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∈ GlobalTheory.ChiGrid.S1 D → GlobalTheory.LamTie.Over4 D.host w := by
    intro w h
    rcases (GlobalTheory.ChiGrid.S1_mem_OmF D).1 h with h | h | h | h
    · exact Or.inl ⟨0, GlobalTheory.BigTop.Fun.natCast_mem_of_under h⟩
    · exact Or.inl ⟨1, GlobalTheory.BigTop.Fun.natCast_mem_of_under h⟩
    · exact Or.inr (Or.inl (GlobalTheory.BigTop.Fun.natCast_mem_of_under h))
    · exact Or.inr (Or.inr (GlobalTheory.BigTop.Fun.natCast_mem_of_under h))
  have a1 : 1 ≤ a.1 + 1 := by omega
  have a2 : a.1 + 1 ≤ D.R.m := a.2
  refine ⟨GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (G.ch.chi_eq _ a1 a2), G.ch.triv _ a1 a2,
    GlobalTheory.BigTop.Fun.lamOf_hasInfQ G a, fun w h4 h0 => ?_, fun w h4 => ?_, fun w he => ?_⟩
  · refine G.ch.unr _ a1 a2 w fun hw => ?_
    rcases G.pl.mem_S0_of_sum_eq.1 hw with h | h
    · exact h0 (h.trans hw0.symm)
    · exact h4 (hOv w h)
  · obtain ⟨l2, l1⟩ := G.ch.lev1 _ a1 a2 w (hS1 w h4)
    exact GlobalTheory.LamTie.GridCharacters.expAt_succ (n := 1) l2 l1
  · have e : w.under (𝓞 D.host.F) = G.pl.v0 :=
      (show w.under (𝓞 D.host.F) = (G.pl.w G.pl.v0).under (𝓞 D.host.F) from he).trans hw0
    obtain ⟨l1, l0⟩ := G.ch.lev0 _ a1 a2 w e
    exact GlobalTheory.LamTie.GridCharacters.expAt_succ (n := 0) l1 fun h => l0 (((G.ch.chiH _).unrAt_iff w).2 h)

end GlobalTheory.GridLambdaData
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.FrobSame

open Polynomial

theorem multiset_eq_of_esymm {s t : Multiset ℂ} {r : ℕ} (hs : Multiset.card s = r) (ht : Multiset.card t = r)
    (h : ∀ k, 1 ≤ k → k ≤ r → s.esymm k = t.esymm k) : s = t := by
  have hall : ∀ k, s.esymm k = t.esymm k := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Multiset.esymm]
    · by_cases hkr : k ≤ r
      · exact h k hk hkr
      · rw [Multiset.esymm, Multiset.esymm, Multiset.powersetCard_eq_empty _ (by omega),
          Multiset.powersetCard_eq_empty _ (by omega)]
  have hp : (s.map fun a => X - C a).prod = (t.map fun a => X - C a).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hs, ht]
    simp only [hall]
  rw [← Polynomial.roots_multiset_prod_X_sub_C s, ← Polynomial.roots_multiset_prod_X_sub_C t, hp]

end GlobalTheory.FrobSame

namespace GlobalTheory.FrobSame

theorem frobEig_eq_of_eig_eq : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (Sb : Finset (PlE D.host)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0), GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ σ σ' : D.what₂.FT, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → D.what₂.isot j σ' ≠ ⊥ → D.nd.goodRow σ' → ∀ P : PlE D.host, IsSplitPl D.host P → P ∉ Sb → (∀ k, 1 ≤ k → k ≤ D.R.r → eig j σ' k P = eig j σ k P) → D.naut.frobEig (Rw.locR σ' P) = D.naut.frobEig (Rw.locR σ P) := by
  intro D cf Rw Sb eig hE hC j hj1 hjm σ σ' hσ hgσ hσ' hgσ' P hP hPS heq
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < D.R.m := by omega
  obtain ⟨hu, he⟩ := hE ⟨i, hi⟩ σ hσ hgσ P hP hPS
  obtain ⟨hu', he'⟩ := hE ⟨i, hi⟩ σ' hσ' hgσ' P hP hPS
  obtain ⟨π, hπ⟩ := hC (i + 1) hj1 hjm σ hσ hgσ
  obtain ⟨π', hπ'⟩ := hC (i + 1) hj1 hjm σ' hσ' hgσ'
  have hcard : (D.naut.frobEig (Rw.locR σ P)).card = D.R.r := by
    rw [D.naut.frobEig_card _ hu, ← hπ.2.2.1 P hP, D.naut.locG_dim]
  have hcard' : (D.naut.frobEig (Rw.locR σ' P)).card = D.R.r := by
    rw [D.naut.frobEig_card _ hu', ← hπ'.2.2.1 P hP, D.naut.locG_dim]
  have hq0 : ((Formalism.ConjugateSelfDual.normV P : ℕ) : ℂ) ≠ 0 := by
    have e : Formalism.ConjugateSelfDual.normV P = Ideal.absNorm P.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    rw [e]; exact_mod_cast GlobalTheory.GalChar.absNorm_ne_zero P
  let f : ℂ → ℂ := fun a => a⁻¹ * (((cf.mu0 ⟨i, hi⟩).val P : ℂˣ) : ℂ)⁻¹ * (((Formalism.ConjugateSelfDual.normV P : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹
  have hfi : Function.Injective f := by
    intro a b hab
    have hc : (((cf.mu0 ⟨i, hi⟩).val P : ℂˣ) : ℂ)⁻¹ * (((Formalism.ConjugateSelfDual.normV P : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹ ≠ 0 :=
      mul_ne_zero (inv_ne_zero (Units.ne_zero _)) (inv_ne_zero (pow_ne_zero _ hq0))
    simp only [f, mul_assoc] at hab
    exact inv_injective (mul_right_cancel₀ hc hab)
  have hmap : (D.naut.frobEig (Rw.locR σ' P)).map f = (D.naut.frobEig (Rw.locR σ P)).map f := by
    refine multiset_eq_of_esymm (r := D.R.r) (by rw [Multiset.card_map, hcard'])
      (by rw [Multiset.card_map, hcard]) fun k hk1 hkr => ?_
    have e1 := he k hk1 hkr
    have e2 := he' k hk1 hkr
    rw [heq k hk1 hkr, e1] at e2
    exact (mul_left_cancel₀ (pow_ne_zero (k * (D.R.r - k) / 2) hq0) e2).symm
  exact Multiset.map_injective hfi hmap

end GlobalTheory.FrobSame
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspFrobSplit

theorem esymm_map_mul_const (s : Multiset ℂ) (c : ℂ) (k : ℕ) :
    (s.map (fun x => x * c)).esymm k = c ^ k * s.esymm k := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, ← Multiset.sum_map_mul_left]
  congr 1
  refine Multiset.map_congr rfl fun t ht => ?_
  have hk : Multiset.card t = k := (Multiset.mem_powersetCard.1 ht).2
  simp only [Function.comp_apply, Multiset.prod_map_mul, Multiset.map_id', Multiset.map_const',
    Multiset.prod_replicate, hk]
  ring

theorem galPol_lifts_ae : ∀ (D : D7) (cf : CharFrame D) (Rw : GlobalTheory.HeightCounting.RowSide D) (Sb : Finset (PlE D.host)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0), ValLL0 D cf → GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig → ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → ∀ π : D.naut.CG D.R.r, D.naut.csd π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = Rw.locR σ w) → ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∈ Polynomial.lifts (embLL0 D) := by
  intro D cf Rw Sb eig hV hE j hj1 hj2 σ hiso hgood π hcsd hloc
  obtain ⟨bar, hinj, hbar⟩ := GlobalTheory.ConjPoly.exists_conj D
  let j' : Fin D.R.m := ⟨j - 1, by omega⟩
  have hjj : (j' : ℕ) + 1 = j := by simp only [j']; omega
  have hfin : (bar ⁻¹' ((Sb : Set (PlE D.host)) ∪ {v | ¬ (cf.mu0 j').UnrAt v})).Finite :=
    (Sb.finite_toSet.union (GlobalTheory.Mem.UnrAe.finite_ramified _)).preimage hinj.injOn
  refine Filter.eventually_cofinite.2 (hfin.subset ?_)
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  by_contra hw'
  apply hw
  intro hsplit
  simp only [Set.mem_preimage, Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hw'
  obtain ⟨hSb, hunrμ⟩ := hw'
  obtain ⟨hc, -, hsp⟩ := hbar w
  have hPs : IsSplitPl D.host (bar w) := hsp hsplit
  have hE' := hE j' σ (by rw [hjj]; exact hiso) hgood (bar w) hPs hSb
  rw [hjj] at hE'
  obtain ⟨hunrP, heig⟩ := hE'
  rw [← hloc (bar w) hPs] at hunrP heig
  obtain ⟨hunrw, hfw⟩ := D.naut.csd_unr π (bar w) w hcsd (GlobalTheory.ToricDenomCheck.isConj_symm hc) hunrP
  have hfP : D.naut.frobEig (D.naut.locG π (bar w)) =
      (D.naut.frobEig (D.naut.locG π w)).map (fun x => x⁻¹) := by
    rw [hfw, Multiset.map_map]; simp
  have hcard : (D.naut.frobEig (D.naut.locG π w)).card = D.R.r := by
    rw [D.naut.frobEig_card _ hunrw, D.naut.locG_dim]
  have hmemS : ∀ x, x ∈ (embLL0 D).fieldRange → x ∈ Set.range (embLL0 D) :=
    fun x h => (RingHom.mem_fieldRange).1 h
  have hNS : ∀ n : ℕ, (n : ℂ) ∈ (embLL0 D).fieldRange := fun n => natCast_mem _ n
  have hN0 : (Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ≠ 0 := by exact_mod_cast GlobalTheory.ConjPoly.normV_ne_zero (bar w)
  have hμ0 : (((cf.mu0 j').val (bar w) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  obtain ⟨yμ, hyμ⟩ := hV.mu0 j' (bar w) hunrμ
  have hμS : (((cf.mu0 j').val (bar w) : ℂˣ) : ℂ) ∈ (embLL0 D).fieldRange :=
    ⟨yμ, by rw [hyμ]; simp [Formalism.L2.Host.HChar.valTw]⟩
  have hAk : ∀ k, 1 ≤ k → k ≤ D.R.r →
      (D.naut.frobEig (D.naut.locG π w)).esymm k ∈ (embLL0 D).fieldRange := by
    intro k hk1 hk2
    have h := heig k hk1 hk2
    rw [hfP, Multiset.map_map] at h
    have hfun : (fun a : ℂ => a⁻¹ * (((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
          ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) ∘ (fun x : ℂ => x⁻¹) =
        fun x => x * ((((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
          ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) := by
      funext x; simp [mul_assoc]
    rw [hfun, esymm_map_mul_const] at h
    have hd : ((((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
        ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) ≠ 0 := by
      simp [hμ0, hN0]
    have hdS : ((((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
        ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) ∈ (embLL0 D).fieldRange :=
      Subfield.mul_mem _ (Subfield.inv_mem _ hμS) (Subfield.inv_mem _ (Subfield.pow_mem _ (hNS _) _))
    have hpow : ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (k * (D.R.r - k) / 2)) ≠ 0 := pow_ne_zero _ hN0
    have heq : (D.naut.frobEig (D.naut.locG π w)).esymm k =
        D.what₂.embLL ↑(eig j σ k (bar w)) * ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (k * (D.R.r - k) / 2))⁻¹ *
          (((((cf.mu0 j').val (bar w) : ℂˣ) : ℂ)⁻¹ *
            ((Formalism.ConjugateSelfDual.normV (bar w) : ℂ) ^ (D.R.nV / 2))⁻¹) ^ k)⁻¹ := by
      rw [h]; field_simp
    rw [heq]
    refine Subfield.mul_mem _ (Subfield.mul_mem _ ⟨eig j σ k (bar w), rfl⟩
      (Subfield.inv_mem _ (Subfield.pow_mem _ (hNS _) _))) (Subfield.inv_mem _ (Subfield.pow_mem _ hdS _))
  have hr : Odd D.R.r := by
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    have := D.R.two_le_m
    exact ⟨a + b - 1, by simp only [Formalism.BasicNotions.Ranks.r]; omega⟩
  obtain ⟨q, hq⟩ := hr
  have hs : ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℂ) ^ ((((1 - (D.R.r : ℝ)) / 2 : ℝ)) : ℂ) =
      ((Formalism.ConjugateSelfDual.normV w : ℂ) ^ q)⁻¹ := by
    have : ((((1 - (D.R.r : ℝ)) / 2 : ℝ)) : ℂ) = -(q : ℂ) := by
      rw [hq]; push_cast; ring
    rw [this, Complex.cpow_neg, Complex.cpow_natCast]
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  unfold Formalism.MainNotions.N.galPol
  rw [D.naut.frobEig_tw _ _ hunrw, hs]
  have hBk : ∀ k, k ≤ D.R.r →
      ((D.naut.frobEig (D.naut.locG π w)).map (fun x => x * ((Formalism.ConjugateSelfDual.normV w : ℂ) ^ q)⁻¹)).esymm k ∈
        (embLL0 D).fieldRange := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have : Multiset.esymm ((D.naut.frobEig (D.naut.locG π w)).map (fun x => x * ((Formalism.ConjugateSelfDual.normV w : ℂ) ^ q)⁻¹)) 0 = 1 := by
        simp [Multiset.esymm, Multiset.powersetCard_zero_left]
      rw [this]; exact Subfield.one_mem _
    rw [esymm_map_mul_const]
    exact Subfield.mul_mem _ (Subfield.pow_mem _ (Subfield.inv_mem _ (Subfield.pow_mem _ (hNS _) _)) _)
      (hAk k hk1 hk)
  have hBc : ((D.naut.frobEig (D.naut.locG π w)).map
      (fun x => x * ((Formalism.ConjugateSelfDual.normV w : ℂ) ^ q)⁻¹)).card = D.R.r := by
    rw [Multiset.card_map, hcard]
  rcases le_or_gt n D.R.r with hn | hn
  · rw [Multiset.prod_X_sub_C_coeff _ (hBc.symm ▸ hn), hBc]
    exact hmemS _ (Subfield.mul_mem _ (Subfield.pow_mem _ (Subfield.neg_mem _ (Subfield.one_mem _)) _)
      (hBk _ (by omega)))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (by rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hBc]; exact hn)]
    exact ⟨0, map_zero _⟩

end GlobalTheory.CuspFrobSplit
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.LabAllOf

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem labAll_of_labTrue_labConj : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), LabTrue D T → LabConj D T →
    GlobalTheory.PendOf.LabAll D T := by
  intro D T hT hC
  have key : ∀ (k : Fin 2) (w : PlE D.host), ∃ γ : G D.host.E D.nd.Om,
      (∀ v, w = D.naut.plGw k v → γ = D.ntypes.tg k v) ∧
      ∀ v, IsConjPl D.host (D.naut.plGw k v) w → ∃ c : D.nd.Om ≃+* D.nd.Om,
        (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
        (∀ x, x ∈ D.nd.plOm.1 (D.naut.plGw k v) ↔ c x ∈ D.nd.plOm.1 w) ∧ (∀ x, γ (c x) = c (D.ntypes.tg k v x)) ∧
        ∀ a : D.naut.LP w, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
          D.naut.items₂ k w a = GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) γ (T.e w a) := by
    intro k w
    by_cases h : ∃ v, IsConjPl D.host (D.naut.plGw k v) w
    · obtain ⟨v, hv⟩ := h
      obtain ⟨c, γ, h1, h2, h3, h4⟩ := hC k v w hv
      refine ⟨γ, fun v' e => absurd (e ▸ hv) (D.naut.plGw_nconj k v v'), fun v' hv' => ?_⟩
      obtain rfl : v = v' := D.naut.plGw_inj k (GlobalTheory.HeightCounting.LabConjModel.eq_of_isConjPl hv hv')
      exact ⟨c, h1, h2, h3, h4⟩
    · refine ⟨Function.extend (D.naut.plGw k) (D.ntypes.tg k) (fun _ => 1) w, fun v e => ?_,
        fun v hv => absurd ⟨v, hv⟩ h⟩
      rw [e]; exact (D.naut.plGw_inj k).extend_apply _ _ v
  choose γ h1 h2 using key
  refine ⟨γ, fun k v => h1 k _ v rfl, fun k v w' hw' => ?_, fun k w hw a => ?_⟩
  · obtain ⟨c, hc1, hc2, hc3, -⟩ := h2 k w' v hw'
    exact ⟨c, hc1, hc2, hc3⟩
  · obtain ⟨v, rfl | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
    · rw [h1 k _ v rfl]; exact hT k v a
    · obtain ⟨c, -, -, -, h4⟩ := h2 k w v hv
      exact h4 a

end GlobalTheory.LabAllOf

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.GreenSide

open Polynomial

theorem eSerC_eq_of_gen (hG : GlobalTheory.Published.GreenCuspidal) (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g)
    (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (z : ℕ → Formalism.CyclotomicNorms.Fbar g) (hz : IsGenSys z) (he : z = L.gen) (htL : t = L.teich)
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) (convC t ht z hz))
    (hO : ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple τ →
      Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (convC t ht z hz) τ (O.lab d τ))
    (r : ℕ) (f : (ZMod g)[X]) (hr : 1 ≤ r) : GlobalTheory.GLq.eSerC L r f = eSerO O r f := by
  subst he
  exact GlobalTheory.T.greenSeriesIdempotent_eq_classFunctionIdempotent hG g L t ht hz htL O hO r f hr

theorem exists_greenLab : GlobalTheory.Published.GreenCuspidal → ∀ (D : D7) (cf : CharFrame D) (Γ : GrpSide D), TypesTrue D.ntypes cf.P cf.W → (∀ k, Γ.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨D.host.g_prime k⟩ (@GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩)) → ∃ Γ' : GrpSide D, GlobalTheory.PendOf.GreenLab Γ' ∧ ∀ k, Γ'.ζ k = Γ.ζ k := by
  intro hG D cf Γ hT hζ
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  have key : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      ∃ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k))
          (convC (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k)),
        Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O ∧ LabTwLawO O ∧
        (∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod (D.host.g k)))), 1 ≤ d → CategoryTheory.Simple τ →
          Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod (D.host.g k)) τ →
          Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (convC (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k)) τ
            (O.lab d τ)) ∧
        ∀ f, D.ntypes.eSer k f = eSerO O D.R.r f := by
    intro k
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    obtain ⟨O, h1, h2, hO⟩ := GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel (ZMod (D.host.g k)) _
      (GlobalTheory.T.cuspParam_of_greenParametrisation hG (D.host.g k) (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k))
    exact ⟨O, h1, h2, hO, fun f => (hT.ser k f).trans
      (eSerC_eq_of_gen hG _ _ _ _ _ _ (hζ k) (hT.teich k) O hO D.R.r f hr)⟩
  refine ⟨{ Γ with
    O := fun k => (key k).choose
    eSer_def := fun k f => (key k).choose_spec.2.2.2 f
    O_equiv := fun k => (key k).choose_spec.1
    O_tw := fun k => (key k).choose_spec.2.1 }, ?_, fun _ => rfl⟩
  intro k d
  exact (key k).choose_spec.2.2.1 d

end GlobalTheory.GreenSide

end
end
