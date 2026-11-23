module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualSplitLabelOperatorMulScalarOperator
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle167
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle212
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle159
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle205
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle224
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle232
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle246
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle177
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle247
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle248
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle149
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.MuTameQS

theorem val_lt_one_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) y < 1 ↔ Valued.v y < 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one

theorem val_eq_one_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) y = 1 ↔ Valued.v y = 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one

theorem isTame_loc {E : Type} [Field E] [NumberField E] {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    (h : χ.TameAt w) : GlobalTheory.SplitWeil.IsTame (χ.loc w) := by
  intro x hx
  have h1 : Valued.v ((x : w.adicCompletion E) - 1) < 1 := (val_lt_one_iff w _).1 hx
  refine h x ?_ ?_
  · have := Valuation.map_one_add_of_lt _ h1
    rwa [add_sub_cancel] at this
  · rw [← WithZero.exp_zero] at h1
    exact WithZero.lt_mul_exp_iff_le (by simp) |>.1 (by simpa [← WithZero.exp_add] using h1)

theorem not_isUnram_loc {E : Type} [Field E] [NumberField E] {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    (h : ¬ χ.UnrAt w) : ¬ GlobalTheory.SplitWeil.IsUnram (χ.loc w) := fun hu =>
  h fun x hx => hu x ((val_eq_one_iff w _).2 hx)

theorem tameAt_mul {E : Type} [Field E] [NumberField E] {χ χ' : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    (h : χ.TameAt w) (h' : χ'.TameAt w) : (χ * χ').TameAt w := fun x hx hx' => by
  change χ.loc w x * χ'.loc w x = 1
  rw [h x hx hx', h' x hx hx', one_mul]

theorem unrAt_mul {E : Type} [Field E] [NumberField E] {χ χ' : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    (h : χ.UnrAt w) (h' : χ'.UnrAt w) : (χ * χ').UnrAt w := fun x hx => by
  change χ.loc w x * χ'.loc w x = 1
  rw [h x hx, h' x hx, one_mul]

theorem unrAt_of_mul_left {E : Type} [Field E] [NumberField E] {χ χ' : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    (h : χ.UnrAt w) (h' : (χ * χ').UnrAt w) : χ'.UnrAt w := fun x hx => by
  have := h' x hx
  change χ.loc w x * χ'.loc w x = 1 at this
  rwa [h x hx, one_mul] at this

end GlobalTheory.MuTameQS
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → _root_.Formalism.DivisionValues.conjPl P ≠ P → UnrPl P χS → UnrPl P χT → VacFix ψ om P ∧ ∀ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ) (t : ℕ), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → (T.rank = S.rank + t → ∀ k, k ≤ T.rank → Match ψ om P (dualC (splitC S.rank fun j => if j ≤ k then (Ideal.absNorm P.asIdeal : ℂ) ^ ((S.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) t (k - j) : ℂ) * ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ S.rank)⁻¹ ^ k * ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ T.rank) ^ j else 0)) (Finsupp.single (splitLab T.rank k) 1)) ∧ (S.rank = T.rank + t → ∀ k, k ≤ S.rank → Match ψ om P (dualC (Finsupp.single (splitLab S.rank k) 1)) (splitC T.rank fun j => if j ≤ k then (Ideal.absNorm P.asIdeal : ℂ) ^ ((T.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) t (k - j) : ℂ) * ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ T.rank)⁻¹ ^ k * ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ S.rank) ^ j else 0)) := by
  first | exact @GlobalTheory.Hk3.SplitMatch.match_split | exact GlobalTheory.Hk3.SplitMatch.match_split | (intros; apply GlobalTheory.Hk3.SplitMatch.match_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CentralShift

open Formalism.L2.NTheta GlobalTheory.SplitPlace GlobalTheory.DualSplitRel

variable {D : D7}

theorem split_of_primeIdem {P : Pl D.host.E} (hP : _root_.Formalism.DivisionValues.conjPl P ≠ P) {e f : AE D} (h : IsPrimeIdem P e f) :
    IsIdemAt e P ∧ f = e + cA D e := by
  rcases h with h | ⟨-, ⟨v, ε, -, rfl⟩, ht⟩
  · exact h
  · refine absurd (GlobalTheory.IdemSupport.eq_of_le (Ideal.map_le_iff_le_comap.2 fun x hx => ?_)) hP
    have h2 := GlobalTheory.IdemSupport.Comparison₂.conj (P := P) ht
    rw [GlobalTheory.IdemSupport.cA_algebraMap] at h2
    by_cases h0 : x = 0
    · rw [h0]; exact zero_mem _
    · exact (h2 x h0).2 ((ht x h0).1 hx)

theorem dual_shift (d : List ℤ) : dualLab ((dualLab (d.map fun x => x - 1)).map (· - 1)) = d := by
  simp [dualLab, List.map_reverse, List.map_map, Function.comp_def]

theorem shift {P : Pl D.host.E} (hP : _root_.Formalism.DivisionValues.conjPl P ≠ P) {V : HSp D} {d : List ℤ} {R : Finset (GA D V)} [DecidableEq (GA D V)]
    (hR : SphOp V P d R) : ∃ z : GA D V, (∀ γ ∈ R, γ * z = z * γ) ∧
      SphOp V P (splitLab V.rank V.rank) {z} ∧ SphOp V P (d.map fun x => x - 1) (R.image (· * z)) := by
  obtain ⟨e, f, ϖ, α, -, hpi, h1, h2, hd, -, -, hα, hD, hRs, hc⟩ := hR
  obtain ⟨he, rfl⟩ := split_of_primeIdem hP hpi
  have h0 : (ϖ : D.host.E) ≠ 0 := GlobalTheory.SphLabelOps.unif_ne_zero h2
  obtain ⟨z, hs, hzc, hz⟩ := exists_central he.1 V h0
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V P
  have hKl : locPart V (KsphC V ∅) e = (K : Set (GA D V)) := (hyp_eq_locPart he V).symm.trans hK
  have hKz : ∀ k ∈ locPart V (KsphC V ∅) e, k * z = z * k := fun k hk => hzc k hk.2
  have sh : ∀ {d : List ℤ} {g : GA D V} {R' : Finset (GA D V)}, SuppAt e V g → DivAt V e (ϖ : D.host.E) d g →
      (∀ γ ∈ R', SuppAt e V γ) → IsCosetRep V (locPart V (KsphC V ∅) e) g R' →
      (d.map (· - 1)).Pairwise (fun a b => b ≤ a) → SphOp V P (d.map (· - 1)) (R'.image (· * z)) := by
    intro d g R' sg dg sR hr hp
    obtain ⟨a, b⟩ := coset_mul hKz (fun γ hγ => (hr.1 γ hγ).2) hr.2
    have sup : ∀ γ ∈ R'.image (· * z), SuppAt e V γ := fun γ hγ => by
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ
      exact suppAt_mul (sR δ hδ) hs
    exact sphOp_of he h1 h2 hp (suppAt_mul sg hs) (divAt_mul h0 hz dg) sup
      ⟨fun γ hγ => ⟨mem_GfC he.1 (sup γ hγ), a γ hγ⟩, b⟩
  have one : IsCosetRep V (locPart V (KsphC V ∅) e) 1 {1} := by
    have := coset_one K
    rw [← hKl] at this
    refine ⟨fun γ hγ => ⟨?_, this.1 γ hγ⟩, this.2⟩
    rw [Finset.mem_singleton.1 hγ]
    exact one_mem _
  have S0 := sh (GlobalTheory.SplitHecke.suppAt_one V)
    (GlobalTheory.SphLabelOps.divAt_one V he.1.1 (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem (Or.inl ⟨he, rfl⟩)) (ϖ : D.host.E))
    (fun γ hγ => by rw [Finset.mem_singleton.1 hγ]; exact GlobalTheory.SplitHecke.suppAt_one V) one
    (by rw [label_shift_zero]; simp [splitLab, List.pairwise_append, List.pairwise_replicate])
  rw [label_shift_zero, Finset.image_singleton, one_mul] at S0
  refine ⟨z, fun γ hγ => hzc γ (hRs γ hγ), S0, sh hα hD hRs hc ?_⟩
  exact List.pairwise_map.2 (hd.imp fun h => by omega)

theorem isLab_of_shift {P : Pl D.host.E} (hP : _root_.Formalism.DivisionValues.conjPl P ≠ P) {V : HSp D} {d : List ℤ}
    (h : IsLab V P (d.map fun x => x - 1)) : IsLab V P d := by
  obtain ⟨R, e, f, ϖ, α, -, hpi, h1, h2, hd, -, -, hα, hD, -, -⟩ := h
  obtain ⟨he, rfl⟩ := split_of_primeIdem hP hpi
  have h0 : (ϖ : D.host.E) ≠ 0 := GlobalTheory.SphLabelOps.unif_ne_zero h2
  obtain ⟨z, hs, -, hz⟩ := exists_central he.1 V h0
  have D1 := (GlobalTheory.DivDual.divAt_inv_and_mul V e _ _ _ he.1.1 h0 hD).1
  have D2 := divAt_mul h0 hz D1
  have D3 := (GlobalTheory.DivDual.divAt_inv_and_mul V e _ _ _ he.1.1 h0 D2).1
  rw [dual_shift] at D3
  refine GlobalTheory.SphLabelOps.isLab_of_divAt hpi h1 h2 ?_ ?_ D3
  · exact (List.pairwise_map.1 hd).imp fun h => by omega
  · exact suppAt_inv (suppAt_mul (suppAt_inv hα) hs)

theorem central_shift : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), _root_.Formalism.DivisionValues.conjPl P ≠ P → ∀ (d : List ℤ) (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (splitLab V.rank V.rank) 1) (opOf π P (Finsupp.single d 1) u) = opOf π P (Finsupp.single (d.map fun x => x - 1) 1) u := by
  classical
  intro D V P hP d M _ _ π u hu
  have c1 := (GlobalTheory.SphLabelOps.label_operators V P).1
  by_cases hl : IsLab V P d
  · obtain ⟨z, hzR, S0, S1⟩ := shift hP (GlobalTheory.SphLabelOps.sphOp_rep hl)
    have fw := (GlobalTheory.SphLabelOps.label_operators V P).2.1 (Finsupp.single d 1) M π u hu

    rw [← (c1 _ _ S0).2 M π _ fw, ← (c1 _ _ S1).2 M π u hu, Finset.sum_singleton, GlobalTheory.SphLabelOps.opOf_single,
    map_sum, Finset.sum_image (mul_left_injective z).injOn]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [hzR γ hγ, map_mul, Module.End.mul_apply]
  · have hl' : ¬ IsLab V P (d.map fun x => x - 1) := fun h => hl (isLab_of_shift hP h)
    have e0 : rep V P d = ∅ := by rw [Hk3.rep, dite_eq_right hl]
    have e1 : rep V P (d.map fun x => x - 1) = ∅ := by rw [Hk3.rep, dite_eq_right hl']
    rw [GlobalTheory.SphLabelOps.opOf_single π d, e0, Finset.sum_empty, map_zero, GlobalTheory.SphLabelOps.opOf_single, e1,
      Finset.sum_empty]

end GlobalTheory.CentralShift
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3

theorem exists_part_level_vector : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → ∀ j c, R.Wc' j c ≠ ⊥ → ∃ w ∈ R.Wc' j c, w ≠ 0 ∧ w ∈ R.toRealDat.WS F.lv2 false j (sg0 D A3.A) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hW hEx hSch s hOk hGG hU j c hne
  obtain ⟨hCoreF, hSF, -, -, -, hWc, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hW
  have hCore := hCoreF hEx
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨h, -, -, -, hsup, hstab, -, -⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hCore hSch hX R.SF hSF j
  obtain ⟨hid, -, -, -⟩ := eH_laws R.toRealDat F.lv2 hCore hX j
  have hfix : ∀ u ∈ Wcc R.toRealDat R.SF j c, eH R.toRealDat j u = u := by
    intro u hu
    have hr : u ∈ LinearMap.range (eH R.toRealDat j) := hsup ▸ (le_iSup (fun c => Wcc R.toRealDat R.SF j c) c) hu
    obtain ⟨x, rfl⟩ := hr
    rw [← Module.End.mul_apply, hid]
  rw [hWc] at hne ⊢
  obtain ⟨u, huU, hu0, hup⟩ := GlobalTheory.T.exists_level_vector_goodType_stable_subspace (sg0 D A3.A) A3.A.X F.P0 F.ψ0⁻¹ (R.gW j (sg0 D A3.A))
    (Wcc R.toRealDat R.SF j c) hX hGG (fun g => hstab c g) hne (fun u hu => by
      have := hfix u hu
      simpa [eH, RealDat.eC] using this)
  refine ⟨u, huU, hu0, ?_⟩
  have hlev := (GlobalTheory.T.goodForms_baseLevel_iff_goodProjection R.toRealDat F.lv2 hCore hX j u).2 ⟨hfix u huU, hup⟩
  have hL := GlobalTheory.LevelForms.levelW_of_irr R.toRealDat F.lv2 hX hU hCore.models.HW
  rw [hL false j (sg0 D A3.A)]
  exact hlev

end GlobalTheory.Hk3
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.DelA

theorem sgRev_mul_self_eq_one (n : ℕ) : sgRev n * sgRev n = 1 := by
  unfold sgRev
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;> rw [h] <;> norm_num

theorem sgRev_ne_zero_of_sq (n : ℕ) : sgRev n ≠ 0 := fun h => by simpa [h] using sgRev_mul_self_eq_one n

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem det_zT_of_odd {n : ℕ}
    (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (ho : IsOddPos (pos.symm τ).2) :
    (zT X D pos f τ).det = sgRev n * ((f τ).det)⁻¹ := by
  unfold zT
  rw [if_pos ho]
  have : (((f τ)⁻¹).transpose.submatrix id Fin.rev) = (((f τ)⁻¹).transpose.submatrix id (Fin.revPerm : Equiv.Perm (Fin n))) := rfl
  rw [this, Matrix.det_permute', Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rfl

theorem det_zT_of_even {n : ℕ}
    (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (ho : ¬ IsOddPos (pos.symm τ).2) :
    (zT X D pos f τ).det = (f τ).det := by
  unfold zT
  rw [if_neg ho]

def frVarToModel (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (k : GL3Theta.FrV D n) : Var (X.Pj i) :=
  ⟨((posJ X D pos i).symm k.1).1, ((posJ X D pos i).symm k.1).2, (Fin.cast h.symm k.2.1, Fin.cast h.symm k.2.2)⟩

theorem valZ_rename_frVar (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (R0 : MvPolynomial (GL3Theta.FrV D n) ℂ)
    (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    valZ X D pos i h (MvPolynomial.rename (frVarToModel X D pos i h) R0) f = GL3Theta.evFr D R0 (zT X D pos f) := by
  unfold valZ GL3Theta.evFr
  rw [MvPolynomial.eval_rename]
  congr 2
  funext k
  simp [frVarToModel]

end GlobalTheory.TwV.DelA
end

noncomputable section
namespace GlobalTheory.TwV.DelA

theorem realises_of_wtPol : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) {n : ℕ} (h : (X.Pj (j + 1)).m + 1 = n) (ν : D.what₂.Tau → Fin n → ℕ), (∀ τ r, (ν τ r : ℤ) ≤ cT1 X D pos j τ) → ∀ Q : MvPolynomial (GL3Theta.FrV D n) ℂ, Q ∈ WtPol ℂ ν → ∃ R, Realises X D pos (j + 1) h (wT X D pos j) Q R := by
  intro p _ X D pos j n h ν hν Q hQ
  obtain ⟨R0, hR0⟩ := GlobalTheory.T.weightPolynomial_div_detPow_eq_poly_of_blockMatrices X D pos ν (cT1 X D pos j) hν Q hQ
  refine ⟨(∏ τ, if IsOddPos (pos.symm τ).2 then sgRev n ^ (-(wT X D pos j τ - cT1 X D pos j τ)) else 1) •
    MvPolynomial.rename (frVarToModel X D pos (j + 1) h) R0, ?_⟩
  intro f
  have hd : ∀ τ, (f.1 τ).det ≠ 0 := fun τ => (f.2 τ).ne_zero
  have hv := valZ_rename_frVar X D pos (j + 1) h R0 f.1
  unfold valZ at hv
  rw [ev1_eq_prod_det_pow_mul_valZ]
  unfold valZ
  rw [MvPolynomial.smul_eval, hv, hR0 f.1 hd]
  have key : (∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos (j + 1) τ) *
      (∏ τ, if IsOddPos (pos.symm τ).2 then sgRev n ^ (-(wT X D pos j τ - cT1 X D pos j τ)) else 1) *
      (∏ τ, if IsOddPos (pos.symm τ).2 then (f.1 τ).det ^ (-(cT1 X D pos j τ)) else 1) =
      ∏ τ, (f.1 τ).det ^ (-(wT X D pos j τ)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [(GlobalTheory.T.realPlaceBlockWeightLastEntry_consecutive_levels X D pos j τ).2]
    by_cases ho : IsOddPos (pos.symm τ).2
    · simp only [if_pos ho]
      rw [det_zT_of_odd X D pos f.1 τ ho, mul_zpow, inv_zpow']
      have hs : sgRev n ^ (wT X D pos j τ - cT1 X D pos j τ) * sgRev n ^ (-(wT X D pos j τ - cT1 X D pos j τ)) = 1 := by
        rw [← zpow_add₀ (sgRev_ne_zero_of_sq n), add_neg_cancel, zpow_zero]
      have hdd : (f.1 τ).det ^ (-(wT X D pos j τ - cT1 X D pos j τ)) * (f.1 τ).det ^ (-(cT1 X D pos j τ)) =
          (f.1 τ).det ^ (-(wT X D pos j τ)) := by
        rw [← zpow_add₀ (hd τ)]; congr 1; ring
      calc _ = (sgRev n ^ (wT X D pos j τ - cT1 X D pos j τ) * sgRev n ^ (-(wT X D pos j τ - cT1 X D pos j τ))) *
            ((f.1 τ).det ^ (-(wT X D pos j τ - cT1 X D pos j τ)) * (f.1 τ).det ^ (-(cT1 X D pos j τ))) := by ring
        _ = _ := by rw [hs, hdd, one_mul]
    · simp only [if_neg ho, mul_one]
      rw [det_zT_of_even X D pos f.1 τ ho]
  rw [← key]
  ring

end GlobalTheory.TwV.DelA
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.EigStrCalc

theorem odd_rank (R : Ranks) : Odd R.r := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have h2 := R.two_le_m
  exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩

theorem isSplitPl_of_under (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E))
    (h : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F))) : IsSplitPl D.host w := by
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := h
  rw [GlobalTheory.Mem.GoodPlace.isSplitPl_iff]
  by_cases hw : w = P
  · subst hw
    exact ⟨Q, hPQ, HeightOneSpectrum.ext (by simpa [HeightOneSpectrum.under, Ideal.under] using hQ)⟩
  · exact ⟨P, hw, HeightOneSpectrum.ext (by simpa [HeightOneSpectrum.under, Ideal.under] using hP)⟩

theorem normV_eq_absNorm {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) :
    normV w = Ideal.absNorm w.asIdeal := by
  simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end GlobalTheory.EigStrCalc

namespace GlobalTheory.EigStrCalc

theorem inv_block (q : ℕ) (z : ℂ) (t : ℕ) :
    (((List.range t : List ℕ) : Multiset ℕ).map
        fun k : ℕ => z⁻¹ * (q : ℂ) ^ (((((t : ℝ) - 1) / 2 - k : ℝ)) : ℂ)).map (fun a : ℂ => a⁻¹) =
      GlobalTheory.DownLift.str q z t := by
  unfold GlobalTheory.DownLift.str
  have hr : (Multiset.range t) = (Multiset.range t).map (fun k => t - 1 - k) := by
    rw [← Finset.range_val, ← Finset.image_val_of_injOn]
    · rw [show (Finset.range t).image (fun k => t - 1 - k) = Finset.range t from ?_]
      ext k; simp only [Finset.mem_image, Finset.mem_range]; constructor
      · rintro ⟨j, hj, rfl⟩; omega
      · intro hk; exact ⟨t - 1 - k, by omega, by omega⟩
    · intro a ha b hb h; simp only [Finset.coe_range, Set.mem_Iio] at ha hb; simp only at h; omega
  rw [Multiset.map_map]
  conv_rhs => rw [hr, Multiset.map_map]
  have hcoe : ((List.range t : List ℕ) : Multiset ℕ) = Multiset.range t := rfl
  rw [hcoe]
  refine Multiset.map_congr rfl fun k hk => ?_
  rw [Multiset.mem_range] at hk
  simp only [Function.comp_apply]
  rw [mul_inv, inv_inv, ← Complex.cpow_neg]
  congr 2
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

end GlobalTheory.EigStrCalc

namespace GlobalTheory.EigStrCalc

theorem unr_of_speh {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N)
    (θ : A.CG 1) (t : ℕ) (ht : 1 ≤ t) (w : PlE H) (h : A.unr (spehLoc N A ⟨1, θ, t⟩ w)) :
    A.unr (A.locG θ w) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  unfold spehLoc at h
  simp only at h
  rw [List.range_succ_eq_map] at h
  exact (A.unr_tw _ _).1 ((A.unr_sum _ _).1 h).1

end GlobalTheory.EigStrCalc
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.cuspRep_satake_iff_localComponent_satake : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ → (∀ B, (CG.mk π).HasSat w B ↔ GlobalTheory.LFun.HasSatGL w σ.ρ B) ∧ (GlobalTheory.SmGL.IsSpherical σ.ρ ↔ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w (n := a)) ≠ ⊥) := by
  first | (exact @GlobalTheory.Cong.satake_locComp) | (exact GlobalTheory.Cong.satake_locComp) | (intros; apply GlobalTheory.Cong.satake_locComp  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

theorem _root_.GlobalTheory.T.chart_function_field_integral : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → ∀ (I : Finset (Fin (d + 1))), I.Nonempty → ∀ (h : genericPoint Z ∈ I.inf fun i => φ ⁻¹ᵁ chart d i) (y : Z.functionField), y ∈ rB ℂ Z.functionField (crd φ) I → ∃ f : Γ(Z, I.inf fun i => φ ⁻¹ᵁ chart d i), (Z.presheaf.germ _ (genericPoint Z) h).hom f = y := by
  first | (exact @GlobalTheory.PD.XCover.mem_germ_range_of_mem_rB) | (exact GlobalTheory.PD.XCover.mem_germ_range_of_mem_rB) | (intros; apply GlobalTheory.PD.XCover.mem_germ_range_of_mem_rB  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

theorem _root_.GlobalTheory.T.genericGerm_chartInter_integral_coordinateRatios : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → ∀ (I : Finset (Fin (d + 1))), I.Nonempty → ∀ (h : genericPoint Z ∈ I.inf fun i => φ ⁻¹ᵁ chart d i) (f : Γ(Z, I.inf fun i => φ ⁻¹ᵁ chart d i)), (Z.presheaf.germ _ (genericPoint Z) h).hom f ∈ rB ℂ Z.functionField (crd φ) I := by
  first | (exact @GlobalTheory.PD.XCover.germ_mem_rB) | (exact GlobalTheory.PD.XCover.germ_mem_rB) | (intros; apply GlobalTheory.PD.XCover.germ_mem_rB  <;> assumption)
end
