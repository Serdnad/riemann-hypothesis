module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle184
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle423
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle495
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle192
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle400
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle193
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle496
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle497
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle498
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle385
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle493
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactQLat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle212
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section




namespace GlobalTheory.SeeSaw.HzOnto

open GlobalTheory.IwaPlace

variable {D : D7}

def pz (S : HSp D) (z x : Fin S.rank → D.host.E) : D.host.E := ∑ i, ∑ j, star (x i) * S.gram i j * z j

theorem pz_add (S : HSp D) (z x y : Fin S.rank → D.host.E) : pz S z (x + y) = pz S z x + pz S z y := by
  simp only [pz, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem pz_smul (S : HSp D) (z x : Fin S.rank → D.host.E) (c : D.host.E) :
    pz S z (c • x) = star c * pz S z x := by
  simp only [pz, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def valSub (S : HSp D) (M : Lat S) (z : Fin S.rank → D.host.E) : Submodule (𝓞 D.host.E) D.host.E where
  carrier := {a | ∃ x ∈ M, pz S z x = a}
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, M.add_mem hx hy, pz_add S z x y⟩
  zero_mem' := ⟨0, M.zero_mem, by simp [pz]⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    obtain ⟨c', hc'⟩ := GlobalTheory.FinPl.LatMem.star_int c
    refine ⟨c' • x, M.smul_mem c' hx, ?_⟩
    have e : (c' • x : Fin S.rank → D.host.E) = (c' : D.host.E) • x := by
      funext i; exact (algebraMap_smul D.host.E c' (x i)).symm
    rw [e, pz_smul, hc', star_star, Algebra.smul_def]

theorem valSub_isFractional (S : HSp D) (M : Lat S) (hM : IsSelfDualC S M) (z : Fin S.rank → D.host.E) :
    IsFractional (𝓞 D.host.E)⁰ (valSub S M z) := by
  obtain ⟨s, hs⟩ := hM.1.fg
  apply FractionalIdeal.isFractional_of_fg
  let N : Submodule (𝓞 D.host.E) D.host.E := Submodule.span _ (pz S z '' (s : Set _))
  have hle : valSub S M z ≤ N := by
    rintro a ⟨x, hx, rfl⟩
    have hx' : x ∈ Submodule.span (𝓞 D.host.E) (s : Set _) := by rw [hs]; exact hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simpa [pz] using N.zero_mem
    | add x y hx hy ihx ihy => simpa only [pz_add] using N.add_mem ihx ihy
    | smul c x hx ih =>
      obtain ⟨c', hc'⟩ := GlobalTheory.FinPl.LatMem.star_int c
      have e : (c • x : Fin S.rank → D.host.E) = (c : D.host.E) • x := by
        funext i; exact (algebraMap_smul D.host.E c (x i)).symm
      have hc : star (c : D.host.E) = (c' : D.host.E) := hc'.symm
      rw [e, pz_smul, hc, ← Algebra.smul_def]
      exact N.smul_mem c' ih
  exact (Submodule.fg_span (s.finite_toSet.image (pz S z))).of_le hle

def valIdl (S : HSp D) (M : Lat S) (hM : IsSelfDualC S M) (z : Fin S.rank → D.host.E) : FI D :=
  ⟨valSub S M z, valSub_isFractional S M hM z⟩

theorem mem_valIdl {S : HSp D} {M : Lat S} {hM : IsSelfDualC S M} {z : Fin S.rank → D.host.E} {a : D.host.E} :
    a ∈ valIdl S M hM z ↔ ∃ x ∈ M, pz S z x = a := Iff.rfl

theorem hermAt_gen (S : HSp D) (z x : Fin S.rank → D.host.E) (α : Af D.host.F) :
    hermAt S (ratV z) (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) =
      pairA D.host.F 0 α ⊗ₜ[D.host.F] pz S z x := by
  simp only [hermAt, pz, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change (pairA D.host.F 0 α ⊗ₜ[D.host.F] star (1 * x i)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram i j) *
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] z j) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, one_mul]

theorem hermAt_add (S : HSp D) (w x y : Fin S.rank → AE D) : hermAt S w (x + y) = hermAt S w x + hermAt S w y := by
  simp only [hermAt, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hermAt_zero (S : HSp D) (w : Fin S.rank → AE D) : hermAt S w 0 = 0 := by
  simp [hermAt]

theorem hermAt_neg (S : HSp D) (w x : Fin S.rank → AE D) : hermAt S w (-x) = -hermAt S w x := by
  simp [hermAt, Finset.sum_neg_distrib]

theorem cA_sum_eq (S : HSp D) (Z y : Fin S.rank → AE D) :
    cA D (∑ l, (∑ m, cA D (Z m) * gA S m l) * y l) = hermAt S Z y := by
  have hg : ∀ m l, cA D (gA S m l) = gA S l m := fun m l => congrFun (congrFun (adj_gA S) l) m

  simp only [map_sum, map_mul, GlobalTheory.SeeSaw.cA_cA, hermAt, Finset.sum_mul, hg]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_not_intAt (v : Pl D) : ∃ u ∈ idAt D (· = v), u ∉ intAt D (· = v) := GlobalTheory.T.exists_adele_supportedAt_place_not_integral D v

theorem exists_not_mem_idV (v : Pl D) {𝔠 : FI D} (h : 𝔠 ≠ 0) : ∃ t ∈ idAt D (· = v), t ∉ idV 𝔠 v := by
  obtain ⟨x, hx, hg⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔠 h
  obtain ⟨u, hu, hnu⟩ := exists_not_intAt (D := D) v
  have ht : incA D x * u ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ hu
  refine ⟨incA D x * u, ht, fun hm => hnu ?_⟩
  have := ((hg _).1 hm).1
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul] at this

theorem hz_onto : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A L : HSp D) (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) (M : Lat S) (𝔠 : FI D) (v : Pl D), IsSelfDualC S M → LineId o ζ M 𝔠 v → 𝔠 ≠ 0 →
      ∀ g ∈ idV 𝔠⁻¹ v, ∃ y ∈ latV S M (· = v), cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) = g := by
  intro D ψ hψ S A L o ζ M 𝔠 v hM hL h𝔠 g hg
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v
  have hSD := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S M v hM
  set z := vecB o ζ with hzdef
  set 𝔦 : FI D := valIdl S M hM z with h𝔦def
  have hval : ∀ x ∈ latV S M (· = v), hermAt S (ratV z) x ∈ idV 𝔦 v := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hαi, hα, a, ha, m, hm, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      rw [hermAt_gen]
      exact AddSubgroup.subset_closure ⟨α, hαi, hα, _, mem_valIdl.2 ⟨m, hm, rfl⟩, rfl⟩
    | zero => rw [hermAt_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [hermAt_add]; exact add_mem hx hy
    | neg x _ hx => rw [hermAt_neg]; exact neg_mem hx
  have hkey : ∀ t ∈ idAt D (· = v),
      t ∈ idV 𝔠 v ↔ ∀ x ∈ latV S M (· = v), t * hermAt S (ratV z) x ∈ intAt D (· = v) := by
    intro t ht
    rw [← hL t ht, hSD.2.2 (t • ratV z) (fun i => Ideal.mul_mem_right _ _ ht)]
    simp only [GlobalTheory.IwaPlace.SDStable.hermAt_smul_left]
  have h𝔦 : 𝔦 ≠ 0 := by
    intro h0
    obtain ⟨t, ht, htn⟩ := exists_not_mem_idV v h𝔠
    refine htn ((hkey t ht).2 fun x hx => ?_)
    have := hval x hx
    rw [h0, idV_zero, AddSubgroup.mem_bot] at this
    rw [this, mul_zero]
    exact ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  have hsub : ∀ a ∈ idV 𝔦⁻¹ v, a ∈ idV 𝔠 v := by
    intro a ha
    have haA := GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ a ha
    refine (hkey a haA).2 fun x hx => ?_
    have e := (h2 𝔦 1 h𝔦 one_ne_zero a haA).2 (by rwa [one_mul])
    exact (h1 _).1 (e _ (hval x hx))
  have hgA := GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ g hg
  have hg' : g ∈ idV 𝔦 v := by
    have e := (h2 𝔦⁻¹ 1 (inv_ne_zero h𝔦) one_ne_zero g hgA).1 fun a ha =>
      (h2 𝔠 1 h𝔠 one_ne_zero g hgA).2 (by rwa [one_mul]) a (hsub a ha)
    rwa [one_mul, inv_inv] at e
  have honto : ∀ b ∈ idV 𝔦 v, ∃ y ∈ latV S M (· = v), hermAt S (ratV z) y = b := by
    intro b hb
    induction hb using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hαi, hα, a, ha, rfl⟩ := hw
      obtain ⟨m, hm, rfl⟩ := mem_valIdl.1 ha
      exact ⟨_, AddSubgroup.subset_closure ⟨α, hαi, hα, 1, rfl, m, hm, rfl⟩, hermAt_gen S z m α⟩
    | zero => exact ⟨0, zero_mem _, hermAt_zero S _⟩
    | add b b' _ _ hb hb' =>
      obtain ⟨y, hy, e⟩ := hb
      obtain ⟨y', hy', e'⟩ := hb'
      exact ⟨y + y', add_mem hy hy', by rw [hermAt_add, e, e']⟩
    | neg b _ hb =>
      obtain ⟨y, hy, e⟩ := hb
      exact ⟨-y, neg_mem hy, by rw [hermAt_neg, e]⟩
  obtain ⟨y, hy, e⟩ := honto g hg'
  exact ⟨y, hy, by rw [cA_sum_eq, e]⟩

end GlobalTheory.SeeSaw.HzOnto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

namespace GlobalTheory.LastTarget

theorem tensRow_eq_phiOne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n n'' : Type} [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (q : Unif k) (Q : Pair k n)
    (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsFullLattice k] (c : 𝓀[k]ˣ) :
    tensRow (latInd Q.lat Λ) (cosetInd q Q.lat (c • Q).red) = phiOne (c • Q) (lastPair q Λ) := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  have h := ((GlobalTheory.LastSteps.lastTwoSteps k n n n'').2.2.2 q Q.lat Λ).1 ⟨(c • Q).red, (c • Q).red_ne⟩
  funext x
  have hx : withRow (x.submatrix Sum.inl id) (x (Sum.inr 0)) = x := by
    ext i j
    rcases i with i | i
    · rfl
    · fin_cases i; rfl
  have h2 := (h (x.submatrix Sum.inl id) (x (Sum.inr 0))).2
  rw [hx] at h2
  exact h2.symm

end GlobalTheory.LastTarget

namespace GlobalTheory.LastTarget

theorem charInd_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] (χ : AddChar 𝓀[k] ℂ) (Q : Pair k n) : charInd χ Q ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have hne : ∀ a, χ a ≠ 0 := fun a ha => by
    have h1 := AddChar.map_add_eq_mul χ a (-a)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, ha, zero_mul] at h1
    exact one_ne_zero h1
  simp only [charInd, vecInd, Q.lat.zero_mem, if_true, mul_one, Pi.zero_apply] at h0
  exact hne _ h0

theorem lastTarget : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (ζ : Fin L.rank → D.host.E) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ → ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), Matrix.mulVec τ ζ₀ = lam • ζ → valuation k (p.pr (incA D lam)) = 1 → τ.conjTranspose * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∃ ε : 𝓀[k]ˣ, ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → IsSumFrame o'' ζ₀ γ γ₀ → ∀ (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsFullLattice k] (Ψ : Matrix n n' k → ℂ) (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → β.IsLat LS Q.lat → γ.IsLat LT Λ → ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ (charInd (resChar χ hχ q) Q)) Ξ → Vac ψ S T LS LT (· = p.v) Φ₂ → ∀ u : WO A S, ∃ g, Over ψ β γ₀ LS LX g (phiOne (ε • Q) (lastPair q Λ)) (lastBi o o'' τ Ξ Φ₂ u) := by
  intro D k _ _ _ _ p q ψ hψ hU χ hχ hc n n' n'' _ _ _ _ _ _ V₀ A L S X T L'' o o'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  obtain ⟨ε, hε⟩ := GlobalTheory.T.latticePairCharacterIndicator_transform_eq_cosetIndicator D k p q ψ hψ hU χ hχ hc n L S L'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  refine ⟨ε, ?_⟩
  intro α α₀ β γ γ₀ hα hγ Q Λ _ Ψ LS LT LX hLS hLT hLX hβQ hγΛ L₁ L₂ f₁ Ξ Φ₂ hΞ hΦ₂ u
  obtain ⟨g₁, T₁, hg₁, hT₁, hT₁a⟩ := GlobalTheory.T.thetaSlice_lineSum_eq_intertwiner_image D k p n n' ψ hψ hU V₀ A L S o ζ hζ α α₀ β hα Ψ
    (charInd (resChar χ hχ q) Q) (charInd_ne_zero _ Q) LS hLS L₁ L₂ f₁ Ξ hΞ u
  obtain ⟨g₃, T₃, hg₃, hT₃, hT₃b⟩ := hε β LS hLS Q g₁ T₁ hg₁ hT₁
  have hO2 : Over ψ β γ LS LT Φ₂ (latInd Q.lat Λ) Φ₂ :=
    ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D) k p n'' n ψ hψ S T β γ LS LT hLS hLT Φ₂ hΦ₂).2.2 hU Q.lat Λ hβQ hγΛ
  have hrow := tensRow_eq_phiOne q Q Λ ε
  have hSB : tensRow (latInd Q.lat Λ) (cosetInd q Q.lat (ε • Q).red) ∈ SB (Matrix (n'' ⊕ Fin 1) n k) :=
    hrow ▸ GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _
  obtain ⟨g, hg⟩ := GlobalTheory.T.splitPlace_datum_boxTensor_line_over_vacuum D k p n n'' ψ hψ hU S X T L'' o'' ζ₀ hζ₀ β γ γ₀ hγ LS LT LX hLS hLT hLX Φ₂ Φ₂
    (latInd Q.lat Λ) hO2 (cosetInd q Q.lat (ε • Q).red) g₃ T₃ hg₃ hT₃ hSB
  refine ⟨g, ?_⟩
  rw [← hrow]
  have hl : lastBi o o'' τ Ξ Φ₂ u = o''.boxT S Φ₂ (T₃ (rowFun β ζ₀ (cosetInd q Q.lat (ε • Q).red))) := by
    rw [hT₃b, hT₁a]
    rfl
  rw [hl]
  exact hg

end GlobalTheory.LastTarget
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (rowFun)

theorem _root_.GlobalTheory.T.lastSeesaw_datum_eq_lattice_pair_over_vacuum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (ζ : Fin L.rank → D.host.E) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ → ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), Matrix.mulVec τ ζ₀ = lam • ζ → valuation k (p.pr (incA D lam)) = 1 → τ.conjTranspose * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∃ ε : 𝓀[k]ˣ, ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → IsSumFrame o'' ζ₀ γ γ₀ → ∀ (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsFullLattice k] (Ψ : Matrix n n' k → ℂ) (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → β.IsLat LS Q.lat → γ.IsLat LT Λ → ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ (charInd (resChar χ hχ q) Q)) Ξ → Vac ψ S T LS LT (· = p.v) Φ₂ → ∀ u : WO A S, ∃ g, Over ψ β γ₀ LS LX g (phiOne (ε • Q) (lastPair q Λ)) (lastBi o o'' τ Ξ Φ₂ u) := by
  intro D k _ _ _ _ p q ψ hψ hU χ hχ hc n n' n'' _ _ _ _ _ _ V₀ A L S X T L'' o o'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  obtain ⟨ε, hε⟩ := GlobalTheory.T.latticePairCharacterIndicator_transform_eq_cosetIndicator D k p q ψ hψ hU χ hχ hc n L S L'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  refine ⟨ε, ?_⟩
  intro α α₀ β γ γ₀ hα hγ Q Λ _ Ψ LS LT LX hLS hLT hLX hβQ hγΛ L₁ L₂ f₁ Ξ Φ₂ hΞ hΦ₂ u
  have hchar : charInd (resChar χ hχ q) Q ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    have hne : ∀ a, resChar χ hχ q a ≠ 0 := fun a ha => by
      have h1 := AddChar.map_add_eq_mul (resChar χ hχ q) a (-a)
      rw [add_neg_cancel, AddChar.map_zero_eq_one, ha, zero_mul] at h1
      exact one_ne_zero h1
    simp only [charInd, vecInd, Q.lat.zero_mem, ite_true, mul_one, Pi.zero_apply] at h0
    exact hne _ h0
  obtain ⟨g₁, T₁, hg₁, hT₁, hT₁a⟩ := GlobalTheory.T.thetaSlice_lineSum_eq_intertwiner_image D k p n n' ψ hψ hU V₀ A L S o ζ hζ α α₀ β hα Ψ
    (charInd (resChar χ hχ q) Q) hchar LS hLS L₁ L₂ f₁ Ξ hΞ u
  obtain ⟨g₃, T₃, hg₃, hT₃, hT₃b⟩ := hε β LS hLS Q g₁ T₁ hg₁ hT₁
  have hO2 : Over ψ β γ LS LT Φ₂ (latInd Q.lat Λ) Φ₂ :=
    ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D) k p n'' n ψ hψ S T β γ LS LT hLS hLT Φ₂ hΦ₂).2.2 hU Q.lat Λ hβQ hγΛ
  have hrow : tensRow (latInd Q.lat Λ) (cosetInd q Q.lat (ε • Q).red) =
      phiOne (ε • Q) (lastPair q Λ) := by
    let : MeasurableSpace k := borel k
    have : BorelSpace k := ⟨rfl⟩
    have h := ((GlobalTheory.LastSteps.lastTwoSteps k n n n'').2.2.2 q Q.lat Λ).1
      ⟨(ε • Q).red, (ε • Q).red_ne⟩
    funext x
    have hx : withRow (x.submatrix Sum.inl id) (x (Sum.inr 0)) = x := by
      ext i j
      rcases i with i | i
      · rfl
      · fin_cases i; rfl
    have h2 := (h (x.submatrix Sum.inl id) (x (Sum.inr 0))).2
    rw [hx] at h2
    exact h2.symm
  have hSB : tensRow (latInd Q.lat Λ) (cosetInd q Q.lat (ε • Q).red) ∈ SB (Matrix (n'' ⊕ Fin 1) n k) :=
    hrow ▸ GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _
  obtain ⟨g, hg⟩ := GlobalTheory.T.splitPlace_datum_boxTensor_line_over_vacuum D k p n n'' ψ hψ hU S X T L'' o'' ζ₀ hζ₀ β γ γ₀ hγ LS LT LX hLS hLT hLX Φ₂ Φ₂
    (latInd Q.lat Λ) hO2 (cosetInd q Q.lat (ε • Q).red) g₃ T₃ hg₃ hT₃ hSB
  refine ⟨g, ?_⟩
  rw [← hrow]
  have hl : lastBi o o'' τ Ξ Φ₂ u = o''.boxT S Φ₂ (T₃ (rowFun β ζ₀ (cosetInd q Q.lat (ε • Q).red))) := by
    rw [hT₃b, hT₁a]
    rfl
  rw [hl]
  exact hg
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.PlaceInj

theorem under_injective : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → Function.Injective (fun i : {PP // PP ∈ (pk W).Pg ∨ QAll W PP} => HeightOneSpectrum.under (𝓞 D.host.F) i.1) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW
  have lev : (pk W).toLevCh.Is W.P.A3.A.μ0 := hW.bot.hyp.2.2.2.1.lev
  rintro ⟨P, hP⟩ ⟨P', hP'⟩ h
  simp only at h
  apply Subtype.ext
  show P = P'

  have key : ∀ A B : Formalism.L2.DIV.Pl D.host.E, A ∈ (pk W).Pg → (B ∈ (pk W).Pg ∨ QAll W B) →
      A.under (𝓞 D.host.F) = B.under (𝓞 D.host.F) → A = B := by
    intro A B hA hB hAB
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hAB.symm with e | e
    · exact e.symm
    · exfalso
      have hc : Formalism.IndefR.Lev.IsConjPl A B := GlobalTheory.GoodPrimes.isConjPl_iff.2 e
      rcases hB with hB | ⟨t, hB⟩
      · exact (GlobalTheory.ChainEquiv.places_sep _ _ lev W.P.A3.A.μ0).1 A hA B (Or.inl hB) hc
      · exact (GlobalTheory.ChainEquiv.places_sep _ _ lev t).1 A hA B (Or.inr hB) hc
  rcases hP with hP | hP
  · exact key P P' hP hP' h
  · rcases hP' with hP' | hP'
    · exact (key P' P hP' (Or.inr hP) h.symm).symm
    · exact hW.sel P P' hP hP' h

end GlobalTheory.Fam.PlaceInj
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

theorem _root_.GlobalTheory.T.weilCoefficient_externalProduct_eq_mul_orthogonalSum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B W H : HSp D) (o : OrthDec B W H) (χA χW : (AE D)ˣ →* Circle) (omB : WRep A B) (omW : WRep A W) (omH : WRep A H), IsWeilDatumO ψ A B χA χW omB → IsWeilDatumO ψ A W χA χW omW → IsWeilDatumO ψ A H χA 1 omH → ∀ νB 𝓕B νW 𝓕W νH 𝓕H, IsCovolOne (ratL B A) νB 𝓕B → IsCovolOne (ratL W A) νW 𝓕W → IsCovolOne (ratL H A) νH 𝓕H → ∀ Φ Φ', IsThetaFunO ψ A W Φ → IsThetaFunO ψ A H Φ' → ∀ g, wcoef omB νB 𝓕B (o.boxT A Φ Φ') (o.boxT A Φ Φ') g = wcoef omW νW 𝓕W Φ Φ g * wcoef omH νH 𝓕H Φ' Φ' g := by
  first | exact @GlobalTheory.Core.Rk.BoxCoef.wcoef_boxT | exact GlobalTheory.Core.Rk.BoxCoef.wcoef_boxT | (intros; apply GlobalTheory.Core.Rk.BoxCoef.wcoef_boxT <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.doubledLatticeHeightFun_properties : ∀ (D : D7) (A : HSp D) (L : Lat A) (a : GL (Fin A.rank) (AE D)), IsSelfDualC A L → IsMaj A a → Continuous (hgtL A L a) ∧ (∀ g, 0 < hgtL A L a g ∧ hgtL A L a g ≤ 1) ∧ ∀ (Sf : Finset (FinPl D)), IsOpen (openOff A L Sf) ∧ ∀ g ∈ openOff A L Sf, (hgtL A L a g : ℝ) = (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW A a w (projArch D.sp.cm.sig A.gram w g)) * ∏ v ∈ Sf, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v (proj D.sp.cm.sig A.gram v g) := by
  first | exact @GlobalTheory.Core.Rk.IP.hgtL_props | exact GlobalTheory.Core.Rk.IP.hgtL_props | (intros; apply GlobalTheory.Core.Rk.IP.hgtL_props <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.doubling_eulerProduct_farRight : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, SphFactor D → LocalZetaOn D (fun _ => True) → ParamBoundOn D (fun _ => True) → EulerRight D := by
  first | exact @GlobalTheory.Core.Rk.EulerProd.eulerRight | exact GlobalTheory.Core.Rk.EulerProd.eulerRight | (intros; apply GlobalTheory.Core.Rk.EulerProd.eulerRight <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

theorem _root_.GlobalTheory.T.splitPlaceChart_parahoric_level_stabiliser_height : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∧ GlobalTheory.SplitWeil.resCard (Fv D.host.F v) = Ideal.absNorm PP.asIdeal ∧ (∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → GlobalTheory.SplitWeil.IsTame ξl ∧ ¬ GlobalTheory.SplitWeil.IsUnram ξl) ∧ (∀ k < D.R.m, ∀ μ : (Fv D.host.F v)ˣ →* ℂˣ, ((∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (c.chS (k + 1) x)) ∨ (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (c.chT (k + 1) x))) → LiftsChar φ PP μ (w.ξ PP)) ∧ ∀ ι, IsChart s j φ ι → (∃ e : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) ≃ₜ* GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) ∧ (∀ y, e y ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v ↔ y ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) _) ∧ ∀ x ϖ, IsLocUnif φ x ϖ → GlobalTheory.ParHecke.IsHgt ϖ fun y => GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (e y)) ∧ (∀ y, ι y ∈ Lev.levG s.V s.β s.L ↔ y ∈ parahoric (Fv D.host.F v) _ _) ∧ ∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → ∀ y ∈ parahoric (Fv D.host.F v) _ _, ∀ d : (Fv D.host.F v)ˣ, (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → Lev.levChi s.V s.β s.L (ι y) = (((ξl d)⁻¹ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.ChartTwist.chart_dict | exact GlobalTheory.ChartTwist.chart_dict | (intros; apply GlobalTheory.ChartTwist.chart_dict <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.chainTwistPlaces_split_unramifiedQuotients : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → (∀ v, v ∈ c.S ↔ v ∈ w.S₀ ∨ ∃ PP ∈ w.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v) ∧ (∀ PP ∈ w.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ w.S₀) ∧ Set.InjOn (fun PP : Pl D.host.E => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) w.Q ∧ (∀ PP ∈ w.Q, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ∧ Ideal.absNorm ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal = Ideal.absNorm PP.asIdeal ∧ ∃ PP' : Pl D.host.E, PP' ≠ PP ∧ (∀ P : Pl D.host.E, P.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ↔ P = PP ∨ P = PP') ∧ Ideal.absNorm PP'.asIdeal = Ideal.absNorm PP.asIdeal ∧ ∀ i ∈ Finset.Icc 1 D.R.m, ∀ j ∈ Finset.Icc 1 D.R.m, GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP' = (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP)⁻¹) ∧ ∀ i ∈ Finset.Icc 1 D.R.m, ∀ j ∈ Finset.Icc 1 D.R.m, GlobalTheory.LFun.UnrOff (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w.S₀ := by
  first | exact @GlobalTheory.ChainTw.twist_places | exact GlobalTheory.ChainTw.twist_places | (intros; apply GlobalTheory.ChainTw.twist_places <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

theorem _root_.GlobalTheory.T.continuous_flatMap_weilRepresentation_joint : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vU : VolU D ρ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∀ Φ, IsThetaFunO ψ V W Φ → Continuous fun q : (GA D V × GA D W) × Mx D V₀.rank σ × WO V₀ W₀ => flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν (rat x) q.2.1 (om q.1 Φ) q.2.2 := by
  first | exact @GlobalTheory.FlatCont.flatAt_om_continuous | exact GlobalTheory.FlatCont.flatAt_om_continuous | (intros; apply GlobalTheory.FlatCont.flatAt_om_continuous <;> assumption)
end
