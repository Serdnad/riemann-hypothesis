module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevInductionGrowBoundOfPresentation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle344
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle761
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle519
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle688
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle762
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle567
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle746
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle409
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle427
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle764
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle398
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle593
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle175
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle750
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle009
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle765
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrimeUnr

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {i : X.Tw}

theorem vanish (hT : TameQuotient) (_hl : 0 < nu X i) {M : ℕ} {L : Subgroup (GE N)} {p : PlE D.host}
    {d : GE N →* Multiplicative (ZMod (X.l i ^ M))} {σ γ : GE N} (hM : nu X i + 2 ≤ M) (hp : NewPl i M L p d σ γ)
    {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] [TopologicalSpace W] [DiscreteTopology W]
    (ρ : Representation R (GE N) W) (h4 : ∀ m : W, (X.l i ^ (nu X i + 1)) • m = 0) (hρ : ∀ g ∈ DecV N p, ∀ m, ρ g m = m) (z : Z1 ρ)
    (hz : z.1 γ = 0) : ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p), z.1 τ = 0 := by
  have := X.lPrime i
  obtain ⟨h0, -, hn, -, hd, hσ, hγ, hdγ⟩ := hp
  have h8 : normV p % (2 * X.l i ^ (nu X i + 1)) = 1 :=
    KStar.Tree.mod_two_mul_pow_of_le (X.lPrime i).out (by omega) hn
  exact (GlobalTheory.T.tame_relation_cocycle_squareZero_inertia hT D.host.E N.Om (X.l i) (N.plOm.1 p) p (N.plOm.2 p)
    (fun h => h0 p (Or.inl rfl) (X.twistExcludedPlaces_contains_residueChar i h)) (nu X i + 1) h8 M d γ σ (by omega) hd hγ hdγ hσ R W ρ 0 0 h4 (mul_zero _)
    (fun τ hτ m => by rw [mul_zero, zero_smul, add_zero]; exact hρ τ (Ine_le_Dec _ hτ) m)
    (fun m => by rw [zero_smul, add_zero]; exact hρ σ hσ.1 m) z).2 rfl hz

theorem selC_of_vanish : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N) (p : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) (σ γ : GE N), nu X i + 2 ≤ M → Small2 i s M L z → NewPl i M L p d σ γ → ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ), Kills i A → AntiHom X.cc κ → (∀ g ∈ DecV N p, κ g = 1) → ∀ (Q Q' : Finset (PlE D.host)), (∀ v, v ∈ Q' ↔ v ∈ Q ∨ Over p v) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (f : GE N → Fin D.R.r → Y), SelC bkP i s κ Y Q' f → (∀ b, f (two X γ b) = 0) → SelC bkP i s κ Y Q f := by
  intro hT D N X bkP i s hl M L z₀ p d σ γ hM hL hp A _ _ κ hK hκ hκp Q Q' hQ Y _ _ _ _ f hf hγ
  obtain ⟨z, rfl, hz⟩ := hf
  refine ⟨z, rfl, ?_⟩
  have h4 : ∀ m : Fin D.R.r → Y, (X.l i ^ (nu X i + 1)) • m = 0 := fun m => by
    have h1 := hK _ (GlobalTheory.Growth.sq_mem_idl (X := X) (i := i))
    rw [map_natCast] at h1
    rw [← Nat.cast_smul_eq_nsmul A]
    exact (congrArg (· • m) h1).trans (zero_smul _ _)
  have htr : ∀ g ∈ L, ∀ m, repOn (Tgl i s) κ Y g m = ((κ g : Aˣ) : A) • m := fun g hg =>
    (GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl M L z₀ (by omega) hL A κ _ hK (isDual_dualRep i s) Y g hg).1
  have hdec : DecV N p ≤ L := hp.2.2.2.1
  have a1 := vanish hT.1 hl hM hp (repOn (Tgl i s) κ Y) h4
    (fun g hg m => by rw [htr g (hdec hg), hκp g hg, Units.val_one, one_smul]) z (hγ false)
  have a2 := vanish hT.1 hl hM hp ((repOn (Tgl i s) κ Y).comp (cConj X)) h4
    (fun g hg m => by
      change repOn (Tgl i s) κ Y (cConj X g) m = m
      rw [htr _ ((hL.1.2.2.1 g _ (cConj_apply X g)).1 (hdec hg)), antiHom_cConj X hκ, hκp g hg, inv_one, Units.val_one,
        one_smul])
    ⟨fun g => z.1 (cConj X g), z.2.1.comp (GlobalTheory.ResConjTriv.continuous_cConj X), fun g h => by
      change z.1 (cConj X (g * h)) = _
      rw [map_mul]
      exact z.2.2 _ _⟩ (hγ true)
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hz v
  refine GlobalTheory.Growth.mem_bkCond_of hv fun _ h3 => ?_
  by_cases h2 : v ∈ Spl i ∪ (Q' : Set (PlE D.host))
  · rcases h2 with h2 | h2
    · exact absurd (Or.inl h2) h3
    · rcases (hQ v).1 h2 with h5 | rfl | h5
      · exact absurd (Or.inr h5) h3
      · exact Or.inr (GlobalTheory.ResUnr.res_mem_unrAt _ z _ 0 fun τ hτ => by rw [a1 τ hτ, map_zero, sub_self])
      · exact Or.inr (GlobalTheory.ResUnr.res_mem_unrAt_of_conj X h5 _ z a2)
  · exact Or.inl h2

end GlobalTheory.NewPrimeUnr
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrimeRel

theorem one_add_pow_of_sq {B : Type} [CommRing B] {x : B} (hx : x * x = 0) (n : ℕ) : (1 + x) ^ n = 1 + (n : B) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ]
    linear_combination (n : B) * hx

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {i : X.Tw}

theorem tame_rel (hT : TameQuotient) (_hl : 0 < nu X i) {M : ℕ} {L : Subgroup (GE N)} {p : PlE D.host}
    {d : GE N →* Multiplicative (ZMod (X.l i ^ M))} {σ γ : GE N} (hM : nu X i + 2 ≤ M) (hp : NewPl i M L p d σ γ)
    {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] [TopologicalSpace W] [DiscreteTopology W]
    (ρ : Representation R (GE N) W) (a b : R) (h4 : ∀ m : W, (X.l i ^ (nu X i + 1)) • m = 0) (hb : b * b = 0)
    (hI : ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p), ∀ m, ρ τ m = m + (((Multiplicative.toAdd (d τ)).val : R) * b) • m)
    (hσ : ∀ m, ρ σ m = m + a • m) (z : Z1 ρ) : a • z.1 γ = b • z.1 σ := by
  have := X.lPrime i
  obtain ⟨h0, -, hn, -, hd, hσ', hγ, hdγ⟩ := hp
  have h8 : normV p % (2 * X.l i ^ (nu X i + 1)) = 1 :=
    KStar.Tree.mod_two_mul_pow_of_le (X.lPrime i).out (by omega) hn
  exact (GlobalTheory.T.tame_relation_cocycle_squareZero_inertia hT D.host.E N.Om (X.l i) (N.plOm.1 p) p (N.plOm.2 p)
    (fun h => h0 p (Or.inl rfl) (X.twistExcludedPlaces_contains_residueChar i h)) (nu X i + 1) h8 M d γ σ (by omega) hd hγ hdγ hσ' R W ρ a b h4 hb hI hσ z).1

theorem rel : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N) (p : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) (σ γ : GE N), nu X i + 2 ≤ M → Small2 i s M L z → NewPl i M L p d σ γ → ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (κ : GE N →* Bˣ) (x y : B), Kills i B → AntiHom X.cc κ → x * x = 0 → (∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p), ((κ τ : Bˣ) : B) * (1 + x) ^ (Multiplicative.toAdd (d τ)).val = 1) → ((κ σ : Bˣ) : B) * (1 + y) = 1 → ∀ (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) B) Z, Univ bkP i s κ Q Φ Z → ∀ j : Bool × Fin D.R.r, x • Z (two X σ j.1) j.2 - (y * (if j.1 then 1 else ((κ σ : Bˣ) : B))) • Z (two X γ j.1) j.2 ∈ what₂ Φ := by
  intro hT D N X bkP i s hl M L z₀ p d σ γ hM hL hp B _ _ κ x y hK hκ hx hI hσ Q a Φ Z hU j

  let Y := (Fin a → B) ⧸ what₂ Φ
  letI : TopologicalSpace Y := ⊥
  haveI : DiscreteTopology Y := ⟨rfl⟩
  let mk : (Fin a → B) →ₗ[B] Y := (what₂ Φ).mkQ
  have hmk : ∀ v ∈ what₂ Φ, mk v = 0 := fun v hv => (Submodule.Quotient.mk_eq_zero _).2 hv

  let x0 : Fin a → Y := fun j => mk (Pi.single j 1)
  have hrow : ∀ (r : ℕ) (A : Matrix (Fin r) (Fin a) B) (c : Fin r), ∑ j, A c j • x0 j = mk (A c) := by
    intro r A c

    simp only [x0, ← map_smul, ← map_sum]
    congr 1
    ext j
    simp [Pi.single_apply]
  have hx0 : matAct Φ x0 = 0 := by
    ext c
    change ∑ j, Φ c j • x0 j = 0
    rw [hrow]
    exact hmk _ (Submodule.subset_span ⟨c, rfl⟩)
  have hrect : ∀ g c, rect (Z g) x0 c = mk (Z g c) := fun g c => hrow _ _ _

  obtain ⟨z, hz, -⟩ := (hU Y).1 x0 hx0

  have h4 : ∀ m : Fin D.R.r → Y, (X.l i ^ (nu X i + 1)) • m = 0 := fun m => by
    have h1 := hK _ (GlobalTheory.Growth.sq_mem_idl (X := X) (i := i))
    rw [map_natCast] at h1
    rw [← Nat.cast_smul_eq_nsmul B]
    exact (congrArg (· • m) h1).trans (zero_smul _ _)
  have htr : ∀ g ∈ L, ∀ m, repOn (Tgl i s) κ Y g m = ((κ g : Bˣ) : B) • m := fun g hg =>
    (GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl M L z₀ (by omega) hL B κ _ hK (isDual_dualRep i s) Y g hg).1
  have hdec : DecV N p ≤ L := hp.2.2.2.1
  have hIL : ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p), τ ∈ L := fun τ hτ => hdec (Ine_le_Dec _ hτ)
  have hσL : σ ∈ L := hdec hp.2.2.2.2.2.1.1
  have hcL : ∀ g, g ∈ L → cConj X g ∈ L := fun g hg => (hL.1.2.2.1 g _ (cConj_apply X g)).1 hg

  have hIv : ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p),
      ((κ τ : Bˣ) : B) * (1 + ((Multiplicative.toAdd (d τ)).val : B) * x) = 1 := fun τ hτ => by
    rw [← one_add_pow_of_sq hx]
    exact hI τ hτ

  have r1 := tame_rel hT.1 hl hM hp (repOn (Tgl i s) κ Y) (-(y * ((κ σ : Bˣ) : B))) (-x) h4 (by rw [neg_mul_neg, hx])
    (fun τ hτ m => by
      have h := hIv τ hτ
      have hκτ : ((κ τ : Bˣ) : B) = 1 + ((Multiplicative.toAdd (d τ)).val : B) * -x := by
        linear_combination (1 - ((Multiplicative.toAdd (d τ)).val : B) * x) * h +
          ((Multiplicative.toAdd (d τ)).val : B) * ((Multiplicative.toAdd (d τ)).val : B) * ((κ τ : Bˣ) : B) * hx
      rw [htr τ (hIL τ hτ), hκτ, add_smul, one_smul])
    (fun m => by
      have hκσ : ((κ σ : Bˣ) : B) = 1 + -(y * ((κ σ : Bˣ) : B)) := by linear_combination hσ
      rw [htr σ hσL]
      nth_rw 1 [hκσ]
      rw [add_smul, one_smul]) z

  have hcont : Continuous (cConj X) := GlobalTheory.ResConjTriv.continuous_cConj X
  let z' : Z1 ((repOn (Tgl i s) κ Y).comp (cConj X)) :=
    ⟨fun g => z.1 (cConj X g), z.2.1.comp hcont, fun g h => by
      change z.1 (cConj X (g * h)) = _
      rw [map_mul]
      exact z.2.2 _ _⟩
  have r2 := tame_rel hT.1 hl hM hp ((repOn (Tgl i s) κ Y).comp (cConj X)) y x h4 hx
    (fun τ hτ m => by
      change repOn (Tgl i s) κ Y (cConj X τ) m = _
      rw [htr _ (hcL τ (hIL τ hτ)), antiHom_cConj X hκ, Units.inv_eq_of_mul_eq_one_right (hIv τ hτ), add_smul, one_smul])
    (fun m => by
      change repOn (Tgl i s) κ Y (cConj X σ) m = _
      rw [htr _ (hcL σ hσL), antiHom_cConj X hκ, Units.inv_eq_of_mul_eq_one_right hσ, add_smul, one_smul]) z'

  obtain ⟨b, c⟩ := j
  have key : ∀ (u v : B) (g h : GE N), u • z.1 g = v • z.1 h → u • Z g c - v • Z h c ∈ what₂ Φ := by
    intro u v g h e
    have e' := congrFun e c
    simp only [Pi.smul_apply, hz, hrect] at e'
    rw [← Submodule.Quotient.mk_eq_zero (what₂ Φ)]
    change mk (u • Z g c - v • Z h c) = 0
    rw [map_sub, map_smul, map_smul, e', sub_self]
  cases b
  · simp only [two, Bool.false_eq_true, ↓reduceIte, mul_one]
    apply key
    have := r1
    rw [neg_smul, neg_smul, neg_inj] at this
    exact this.symm
  · simp only [two, ↓reduceIte, mul_one]
    apply key
    exact r2.symm

end GlobalTheory.NewPrimeRel
end
end

section

noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellDec
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem cell_lintegral [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] (μ : Measure (GA E n)) [μ.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (hϖ : ∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) (𝓕 : Set (GA E n)) (h𝓕 : IsFundamentalDomain (NE E n) 𝓕 μ)
    (B : GA E n → ℝ≥0∞) (hB : Measurable B) (hinv : ∀ u ∈ NA E n, ∀ g, B (u * g) = B g) :
    ∫⁻ g in 𝓕, B g ∂μ =
      ∑' l : abelian₂ E n S, ENNReal.ofReal (dinv n l.1) * ∫⁻ g in 𝓕 ∩ C0 E n S, B (tl n ϖ l.1 * g) ∂μ := by
  have hC : MeasurableSet (C0 E n S) := (GlobalTheory.T.isOpen_C0 E n S).measurableSet
  let cellS : abelian₂ E n S → Set (GA E n) := fun l => {g | (tl n ϖ l.1)⁻¹ * g ∈ C0 E n S}
  have hmeas : ∀ l, MeasurableSet (cellS l) := fun l =>
    ((GlobalTheory.T.isOpen_C0 E n S).preimage (continuous_const.mul continuous_id)).measurableSet
  have hpart : ∀ g, ∑' l : abelian₂ E n S, (cellS l).indicator B g = B g := by
    intro g
    obtain ⟨l0, hl0S, hl0⟩ := GlobalTheory.T.exists_tl_inv_mul_mem_C0_off_finset E n S ϖ hϖ g
    have hz : ∀ l : abelian₂ E n S, l ≠ (⟨l0, hl0S⟩ : abelian₂ E n S) → (cellS l).indicator B g = 0 := fun l hl =>
      Set.indicator_of_notMem (show g ∉ cellS l from fun hg => hl (Subtype.ext (GlobalTheory.T.adelic_iwasawa_cells_disjoint_off_finset E n S ϖ hϖ l.1 l0 g l.2 hl0S hg hl0))) B
    rw [tsum_eq_single _ hz]
    exact Set.indicator_of_mem (show g ∈ cellS ⟨l0, hl0S⟩ from hl0) _
  calc ∫⁻ g in 𝓕, B g ∂μ = ∫⁻ g in 𝓕, ∑' l, (cellS l).indicator B g ∂μ := by simp_rw [hpart]
    _ = ∑' l, ∫⁻ g in 𝓕, (cellS l).indicator B g ∂μ :=
        lintegral_tsum fun l => (hB.indicator (hmeas l)).aemeasurable
    _ = _ := tsum_congr fun l => ?_
  let t := tl n ϖ l.1
  let F : GA E n → ℝ≥0∞ := (C0 E n S).indicator fun h => B (t * h)
  have e : (cellS l).indicator B = fun g => F (t⁻¹ * g) := by
    funext g
    show (cellS l).indicator B g = (C0 E n S).indicator (fun h => B (t * h)) (t⁻¹ * g)
    by_cases hg : t⁻¹ * g ∈ C0 E n S
    · rw [Set.indicator_of_mem (show g ∈ cellS l from hg), Set.indicator_of_mem hg, mul_inv_cancel_left]
    · rw [Set.indicator_of_notMem (show g ∉ cellS l from hg), Set.indicator_of_notMem hg]
  have hF : Measurable F := (hB.comp (measurable_const_mul t)).indicator hC
  have hFinv : ∀ u ∈ NA E n, ∀ g, F (u * g) = F g := by
    intro u hu g
    show (C0 E n S).indicator (fun h => B (t * h)) (u * g) = (C0 E n S).indicator (fun h => B (t * h)) g
    by_cases hg : g ∈ C0 E n S
    · rw [Set.indicator_of_mem (adelicUnitriangular_mul_mem_unipotentTimesIntegral hu hg), Set.indicator_of_mem hg]
      change B (t * (u * g)) = B (t * g)
      rw [show t * (u * g) = (t * u * t⁻¹) * (t * g) by group]
      exact hinv _ (tl_conj_mem ϖ l.1 hu) _
    · have : u * g ∉ C0 E n S := fun h => hg (by simpa using adelicUnitriangular_mul_mem_unipotentTimesIntegral (inv_mem hu) h)
      rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hg]
  rw [e, GlobalTheory.T.lintegral_uniformizerTorus_translate_unipotentQuotient E n μ ϖ hϖ l.1 𝓕 h𝓕 F hF hFinv]
  congr 1
  rw [lintegral_indicator hC, Measure.restrict_restrict hC, Set.inter_comm]

theorem cell_integral [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] (μ : Measure (GA E n)) [μ.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (hϖ : ∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) (𝓕 : Set (GA E n)) (h𝓕 : IsFundamentalDomain (NE E n) 𝓕 μ)
    (B : GA E n → ℂ) (hB : Measurable B) (hBi : Integrable B (μ.restrict 𝓕))
    (hinv : ∀ u ∈ NA E n, ∀ g, B (u * g) = B g) :
    (∀ l : abelian₂ E n S, Integrable (fun g => B (tl n ϖ l.1 * g)) (μ.restrict (𝓕 ∩ C0 E n S))) ∧
      HasSum (fun l : abelian₂ E n S => (dinv n l.1 : ℂ) * ∫ g in 𝓕 ∩ C0 E n S, B (tl n ϖ l.1 * g) ∂μ)
        (∫ g in 𝓕, B g ∂μ) := by
  have hpos : ∀ l : abelian₂ E n S, 0 < dinv n l.1 := fun l =>
    Finset.prod_pos fun v _ => zpow_pos (by exact_mod_cast (GlobalTheory.LFun.qV_ne_zero v).bot_lt) _
  exact GlobalTheory.T.hasSum_unfolding_of_complex_invariant_integrable μ 𝓕 (𝓕 ∩ C0 E n S) (fun l : abelian₂ E n S => dinv n l.1) hpos (fun l g => tl n ϖ l.1 * g)
    (fun l => measurable_const_mul _) ((fun u : GA E n => fun g => u * g) '' (NA E n : Set (GA E n)))
    (fun f hf hfi => cell_lintegral μ S ϖ hϖ 𝓕 h𝓕 f hf fun u hu g => hfi _ ⟨u, hu, rfl⟩ g)
    B hB hBi (by rintro _ ⟨u, hu, rfl⟩ x; exact hinv u hu x)

end GlobalTheory.CellDec
end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.lastRow_sub_single_not_mem_lattice_of_neg_exponent : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) T) (w : HeightOneSpectrum (𝓞 E)),
      l.1 w (Fin.last m) < 0 →
      (fun i => pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g).val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∉
        GlobalTheory.ThetaPoisson.latt (m + 1) J := by
  first | exact @GlobalTheory.CellDec.lastRow_sub_notMem_latt | exact GlobalTheory.CellDec.lastRow_sub_notMem_latt | (intros; apply GlobalTheory.CellDec.lastRow_sub_notMem_latt <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.lastRow_diagonal_mul_mem_lattice_iff : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) T), (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      ((fun i => pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g).val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈
        GlobalTheory.ThetaPoisson.latt (m + 1) J ↔
      (fun i => pFin E (g.val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J) := by
  first | exact @GlobalTheory.CellDec.lastRow_tl_mul_mem_latt_iff | exact GlobalTheory.CellDec.lastRow_tl_mul_mem_latt_iff | (intros; apply GlobalTheory.CellDec.lastRow_tl_mul_mem_latt_iff <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.ideleModule_det_diagonalUniformiser_mul : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ),
    (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n),
      (ideleModule E (GeneralLinearGroup.det (GlobalTheory.CellDec.tl n ϖ l * g)) : ℝ) =
        (∏ v ∈ l.support, ((qV E v : ℝ) ^ (∑ i, l v i))⁻¹) * (ideleModule E (GeneralLinearGroup.det g) : ℝ) := by
  first | exact @GlobalTheory.CellDec.DetMod.ideleModule_det_tl_mul | exact GlobalTheory.CellDec.DetMod.ideleModule_det_tl_mul | (intros; apply GlobalTheory.CellDec.DetMod.ideleModule_det_tl_mul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

theorem _root_.GlobalTheory.T.exists_supported_unitary_adjoint_action : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι → ∀ γ : GL (Fin T.rank) (Fv D.host.F v), ∃ g : GA D T, SuppAt e T g ∧ ∀ x : WO S T, rdAdj S T βS βT φ (actO S T 1 g x) = rdAdj S T βS βT φ x * γ.val := by
  first | exact @GlobalTheory.DownLift.SplitCoef.exists_supp_rdAdj_mul | exact GlobalTheory.DownLift.SplitCoef.exists_supp_rdAdj_mul | (intros; apply GlobalTheory.DownLift.SplitCoef.exists_supp_rdAdj_mul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.rationalUnitaryLagrangianAction_eq_of_mem_frameUnipotent : ∀ (D : D7) (W : HSp D) (Y : Lag W) (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ n : GQ W, (n : GA D W) ∈ NI W I → GlobalTheory.RallisCusp.lagAct W n Y = Y := by
  first | exact @GlobalTheory.RallisCuspStab.lagAct_eq_of_mem_NI | exact GlobalTheory.RallisCuspStab.lagAct_eq_of_mem_NI | (intros; apply GlobalTheory.RallisCuspStab.lagAct_eq_of_mem_NI <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.lagrangianStabilizer_normalizes_frameUnipotent : ∀ (D : D7) (W : HSp D) (Y : Lag W) (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ γ : GQ W, GlobalTheory.RallisCusp.lagAct W γ Y = Y → ∀ n ∈ NI W I, (γ : GA D W) * n * (γ : GA D W)⁻¹ ∈ NI W I := by
  first | exact @GlobalTheory.RallisCusp.conj_mem_NI | exact GlobalTheory.RallisCusp.conj_mem_NI | (intros; apply GlobalTheory.RallisCusp.conj_mem_NI <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.exists_standardAdelicAddChar : ∀ (E : Type) [Field E] [NumberField E], ∃ ψ : AddChar (Ad E) ℂ, StdPsi ψ := by
  first | exact @GlobalTheory.CuspGeneric.exists_stdPsi | exact GlobalTheory.CuspGeneric.exists_stdPsi | (intros; apply GlobalTheory.CuspGeneric.exists_stdPsi <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.LTChar

theorem exists_crystalline_char_jump_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ χ : ↥(GK K) →* (↥(OL LL))ˣ, Continuous (fun g => (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1)) ∧ IsCrys (P.PD K) (charRep ((Units.map (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom).comp χ)) ∧ ∀ τ b, multV (P.PD K) (charRep ((Units.map (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom).comp χ)) τ b = if b = (if τ = τ₀ then 1 else 0) then 1 else 0 := by
  intro l _ P AI hT K LL hA τ₀
  haveI := (P.PD K).finK₀
  have hn : 0 < finrank ℚ_[l] ↥(K0 K) := Module.finrank_pos
  obtain ⟨x, hxu, hxφ, hx1, hx2, hxj⟩ := GlobalTheory.T.exists_cyclotomic_period_local_prime l P AI hT K _ hn
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_unramified_character_of_eigen_unit l P K x hxu (GlobalTheory.T.galois_periodRatio_mem_unramified_alt l P AI hT K x hxu hxφ hx1 hx2 hxj)
  have hcont := GlobalTheory.T.continuous_galois_character_of_bcris_unit_fil_one l P AI hT K x hxu hx1 hx2 c hc
  obtain ⟨χ, hχc, hχ⟩ := GlobalTheory.T.exists_continuous_integralUnitChar_of_char l K LL τ₀ c hcont
  exact ⟨χ, hχc, GlobalTheory.T.crystalline_character_jump_one_at_embedding l P AI hT K LL hA τ₀ x hxu hxφ hx1 hx2 hxj c hc _ hχc hχ⟩

end GlobalTheory.LTChar
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem _root_.GlobalTheory.T.gamma_operator_semisimple_of_conclusions : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.LiftingTheory.adm19 D HW F := by
  first | exact @GlobalTheory.dss_semisimple_of_used | exact GlobalTheory.dss_semisimple_of_used | (intros; apply GlobalTheory.dss_semisimple_of_used <;> assumption)
end
