module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle154
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle063
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle727
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1795
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

namespace GlobalTheory.GeoLevel

theorem det_mul_cc_det_of_isMatch {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (δ : GL (Fin r) E) (h : IsMatch X X δ) :
    (δ : Matrix (Fin r) (Fin r) E).det * IsCMField.complexConj E (δ : Matrix (Fin r) (Fin r) E).det = 1 := by
  have hm : (δ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm *
      ((IsCMField.complexConj E : E →+* E).mapMatrix (δ : Matrix (Fin r) (Fin r) E)) = X.Gm := by
    ext i j
    have := h.iso (Pi.single i 1) (Pi.single j 1)
    simp only [herm, cc, Matrix.mulVec_single_one, Matrix.col_apply] at this
    simp only [Pi.single_apply, apply_ite, map_one, map_zero, mul_ite, ite_mul, mul_one, one_mul, mul_zero,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    rw [← this]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det] at hd
  apply mul_left_cancel₀ X.Gm_det
  rw [mul_one]
  refine Eq.trans ?_ hd
  rw [← mul_assoc, mul_comm X.Gm.det]
  rfl

theorem four_dvd_finrank_and_det_eq_pm_one : ∀ (D : D7), 4 ∣ Module.finrank ℚ D.host.E ∧ ∀ (r : ℕ) (X : Data D.host.E r) (δ : GL (Fin r) D.host.E), IsMatch X X δ → (δ : Matrix (Fin r) (Fin r) D.host.E).det = 1 ∨ ∃ m : ℕ, 0 < m ∧ (δ : Matrix (Fin r) (Fin r) D.host.E).det ^ m = 1 := by
  intro D
  refine ⟨?_, fun r X δ h => ?_⟩
  · have hE : Module.finrank ℚ D.host.E = 4 * D.R.n := by
      have h : (Module.finrank ℚ D.host.E : ℝ) = 4 * (D.R.n : ℝ) := by
        rw [D.host.finrank_cmField]
        unfold Ranks.n
        push_cast
        ring
      exact_mod_cast h
    exact ⟨_, hE⟩
  · have h1 := det_mul_cc_det_of_isMatch X δ h
    refine Or.inr (GlobalTheory.Mem.StabDet.eq_pm_one_of_unitary D.host _ ⟨?_, h1⟩
      (GlobalTheory.Mem.StabDet.isIntegral_det X.Λ X.Λ_fg X.Λ_span _ fun v hv => (h.lat v).1 hv))
    rw [mul_comm]
    exact h1

end GlobalTheory.GeoLevel
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.DetIdealPrime

theorem exists_ideal_coprime : ∀ (D : D7) (V : HSp D), HSpace.gram V = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (h : GA D V) (e : AE D) (P : Finset (HeightOneSpectrum (𝓞 D.host.E))) (y : (AE D)ˣ), IsIdemSum e P → SuppAt e V h → IsDetAt e V h y → ∀ (b : ℕ), (∀ Q ∈ P, (b : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → ψ.UnrAt Q) → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k : D.host.Fˣ, ψ.resFin (Q.under (𝓞 D.host.F)) k = 1) → ∀ (Λ : GenLat D.host.E V.rank), (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat V (fin V h)) → ∀ p : ℕ, p.Prime → Λ.TrivAt p → ∃ cc : Ideal (𝓞 D.host.E), cc ≠ ⊥ ∧ cc ⊔ Ideal.span {(b : 𝓞 D.host.E)} = ⊤ ∧ Nat.Coprime (Ideal.absNorm cc) p ∧ ((c y : Circle) : ℂ) = ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℂˣ) : ℂ) := by
  intro D V hg hL h e P y he hs hy b hb c ψ hc hu hr Λ hΛ p hp hT
  obtain ⟨cc, c0, c1, c2, c3, c4⟩ := GlobalTheory.ClassScalarValue.exists_ideal V hg hL h e P y he hs hy b hb c ψ hc hu hr
  refine ⟨cc, c0, c2, ?_, c4⟩
  refine GlobalTheory.NormCoprime.coprime_absNorm_of_sup p hp c0 ?_
  obtain ⟨k, hk, -, hk2⟩ := hT
  have hdet : ((k : D.host.E) ^ V.rank) ∈ Submodule.span (𝓞 D.host.E) (detSet (Bridge.hLat V (fin V h))) := by
    refine Submodule.subset_span ⟨fun i => (k : D.host.E) • (Pi.single i 1 : Fin V.rank → D.host.E), fun i => ?_, ?_⟩
    · have hstd : (Pi.single i (1 : D.host.E) : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank := by
        rw [Formalism.L2.Pj.stdLat, Submodule.mem_pi]
        intro j _
        by_cases hj : j = i
        · subst hj; simpa using (Submodule.one_le.1 le_rfl : (1 : D.host.E) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E))
        · simp [Pi.single_apply, hj]
      have h1 := hk2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (k : 𝓞 D.host.E)) hstd)
      have h2 : ((k : 𝓞 D.host.E) • (Pi.single i (1 : D.host.E) : Fin V.rank → D.host.E)) =
          (k : D.host.E) • (Pi.single i 1 : Fin V.rank → D.host.E) := by
        rw [← map_natCast (algebraMap (𝓞 D.host.E) D.host.E) k, algebraMap_smul]
      rw [h2] at h1
      have h3 := (hΛ _).1 h1
      convert h3 using 1
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    · have : (Matrix.of fun i j => ((k : D.host.E) • (Pi.single j 1 : Fin V.rank → D.host.E)) i) =
          (k : D.host.E) • (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) := by
        ext i j
        simp [Matrix.one_apply, Pi.single_apply, eq_comm]
      rw [this, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hcM : cc ≤ M := le_trans le_sup_left hle
  have hpM : ((p : ℕ) : 𝓞 D.host.E) ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hkM : ((k : ℕ) : 𝓞 D.host.E) ∉ M := by
    intro hkM
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hk
    have e1 := congrArg (Int.cast : ℤ → 𝓞 D.host.E) huv
    push_cast at e1
    refine hM.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← e1]
    exact M.add_mem (M.mul_mem_left _ hkM) (M.mul_mem_left _ hpM)
  have hkn : ((k : ℕ) : 𝓞 D.host.E) ^ V.rank ∉ M := fun h0 => hkM (hM.isPrime.mem_of_pow_mem _ h0)
  have hc'M : cc.map (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ M := by
    intro x hx
    have hm : (k : D.host.E) ^ V.rank * (x : D.host.E) ∈ idlE cc := by
      rw [← c3]
      exact Submodule.mul_mem_mul hdet ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzeq⟩ := hm
    have hz' : z = ((k : ℕ) : 𝓞 D.host.E) ^ V.rank * x := by
      apply RingOfIntegers.ext
      rw [show (z : D.host.E) = Algebra.linearMap (𝓞 D.host.E) D.host.E z from rfl, hzeq]
      push_cast
      rfl
    rw [hz'] at hz
    exact ((hM.isPrime.mem_or_mem (hcM hz)).resolve_left hkn)
  exact hM.ne_top (top_le_iff.1 (c1 ▸ sup_le hcM hc'M))

end GlobalTheory.DetIdealPrime
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj.LevRowSucc

open GlobalTheory.AdIsom GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents

variable {D : D7}

theorem mem_O_iff {w : Pl D.host.E} (a : Kw w) : a ∈ 𝒪[Kw w] ↔ Valued.v a ≤ 1 := by
  have : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (valuation (Kw w)) Valued.v).le_one_iff_le_one

theorem inBasis_val {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (i j : Fin n') :
    (inBasis h β w x).val i j = cpt w ((β⁻¹ * x * β).val (Fin.cast h i) (Fin.cast h j)) := by
  simp only [inBasis, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rfl

theorem ent_of_KO {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E)
    (hx : inBasis h β w x ∈ KO (Kw w) (Fin n')) :
    (∀ i j, Valued.v (cpt w ((β⁻¹ * x * β).val i j)) ≤ 1) ∧ ∀ i j, Valued.v (cpt w ((β⁻¹ * x⁻¹ * β).val i j)) ≤ 1 := by
  subst h
  obtain ⟨h1, h2⟩ := (mem_KO_iff _).1 hx
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have := (mem_O_iff _).1 (h1 i j)
    rwa [inBasis_val] at this
  · have := (mem_O_iff _).1 (h2 i j)
    rwa [← map_inv, inBasis_val] at this

theorem KO_of_St {n n' : ℕ} (h : n' = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) {x : GL (Fin n) (Lev.EAf D)}
    (hx : x ∈ St β) : inBasis h β w x ∈ KO (Kw w) (Fin n') := by
  subst h
  obtain ⟨z, rfl⟩ := hx
  have e1 : β⁻¹ * frGL β z * β = intGL D.host.F D.host.E _ z := by
    show β⁻¹ * (β * intGL D.host.F D.host.E _ z * β⁻¹) * β = _
    group
  have e2 : β⁻¹ * (frGL β z)⁻¹ * β = intGL D.host.F D.host.E _ z⁻¹ := by
    rw [← map_inv]
    show β⁻¹ * (β * intGL D.host.F D.host.E _ z⁻¹ * β⁻¹) * β = _
    group
  refine (mem_KO_iff _).2 ⟨fun i j => (mem_O_iff _).2 ?_, fun i j => (mem_O_iff _).2 ?_⟩
  · rw [inBasis_val, e1]
    exact (mem_OA _).1 (z.val _ _).2 w
  · rw [← map_inv, inBasis_val, e2]
    exact (mem_OA _).1 ((z⁻¹).val _ _).2 w

theorem idem_smul_mem {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {β : GL (Fin n) (Lev.EAf D)}
    (hβ : IsFrame β Λ) {w : Pl D.host.E} {x : GL (Fin n) (Lev.EAf D)}
    (hx : ∀ i j, Valued.v (cpt w ((β⁻¹ * x * β).val i j)) ≤ 1) {y : Fin n → Lev.EAf D} (hy : y ∈ hat Λ) :
    idem w • (x.val *ᵥ y) ∈ hat Λ := by
  rw [mem_hat, hβ] at hy ⊢
  intro i
  have e : (β⁻¹).val *ᵥ (idem w • (x.val *ᵥ y)) = idem w • ((β⁻¹ * x * β).val *ᵥ ((β⁻¹).val *ᵥ y)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul,
      Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [e, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  rw [← mul_assoc]
  exact mul_mem ((idem_mul_mem_iff w _).2 (hx i j)) (hy j)

theorem hA_unitary {V : HSp D} {x : GL (Fin V.rank) (Lev.EAf D)} (hx : x ∈ UA D.sp.cm V.gram)
    (a b : Fin V.rank → Lev.EAf D) : hA V (x.val *ᵥ a) (x.val *ᵥ b) = hA V a b := by
  have hx' : Formalism.UG.cT (cjA D) x.val * V.gram.map (inc D) * x.val = V.gram.map (inc D) := hx
  have e2 : ∀ u v : Fin V.rank → Lev.EAf D,
      Formalism.UG.hform (cjA D) (V.gram.map (inc D)) u v = (cjA D ∘ u) ⬝ᵥ (V.gram.map (inc D) *ᵥ v) := by
    intro u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Function.comp_apply, mul_assoc]
  have e3 : cjA D ∘ (x.val *ᵥ b) = (cjA D ∘ b) ᵥ* Formalism.UG.cT (cjA D) x.val := by
    funext i
    rw [Formalism.UG.cT, vecMul_transpose, Function.comp_apply, RingHom.map_mulVec]
  rw [hA_eq, hA_eq, e2, e2, e3, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hx']

theorem transfer {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hsd : IsSelfDualC V Λ)
    {x : GL (Fin V.rank) (Lev.EAf D)} (hU : x ∈ UA D.sp.cm V.gram) {w : Pl D.host.E}
    (h : ∀ y ∈ hat Λ, idem w • ((x⁻¹).val *ᵥ y) ∈ hat Λ) {y : Fin V.rank → Lev.EAf D} (hy : y ∈ hat Λ) :
    idem (GlobalTheory.IdemSupport.cP w) • (x.val *ᵥ y) ∈ hat Λ := by
  rw [mem_hat_iff_of_selfDual hsd]
  intro z hz
  have e : z = x.val *ᵥ ((x⁻¹).val *ᵥ z) := by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  rw [hA_smul_right, cjA_idem, GlobalTheory.StdFrames.cP_cP, e, hA_unitary hU, ← hA_smul_left]
  exact (mem_hat_iff_of_selfDual hsd y).1 hy _ (h z hz)

theorem givenLevel_succ {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E) (a : ℕ) :
    ∀ b, b ≠ 0 → givenLevel G t w (a + 1, b) = KO (Kw w) (Fin ((locGrid G t w).rank (a + 1, b)))
  | 0, h => absurd rfl h
  | _ + 1, _ => rfl




theorem prodLev_inf_UA {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {β : GL (Fin V.rank) (Lev.EAf D)}
    (hβ : IsFrame β Λ) (hsd : IsSelfDualC V Λ) (P : Finset (Pl D.host.E)) {n' : P → ℕ} (hn : ∀ w, n' w = V.rank)
    (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (hK : ∀ w, K w = KO (Kw w.1) (Fin (n' w))) :
    prodLev β P hn K ⊓ UA D.sp.cm V.gram = congLev D.sp.cm V.gram Λ ⊤ := by
  rw [congLev_top]
  have key : ∀ g ∈ prodLev β P hn K ⊓ UA D.sp.cm V.gram, ∀ (Q : Pl D.host.E), ∀ y ∈ hat Λ,
      idem Q • (g.val *ᵥ y) ∈ hat Λ := by
    rintro g hg Q y hy
    obtain ⟨hg, hU⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨hA', hB'⟩ := Subgroup.mem_inf.1 hg
    have hA : ∀ w : P, (∀ i j, Valued.v (cpt w.1 ((β⁻¹ * g * β).val i j)) ≤ 1) ∧
        ∀ i j, Valued.v (cpt w.1 ((β⁻¹ * g⁻¹ * β).val i j)) ≤ 1 := fun w => by
      have := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hA' w)
      rw [hK] at this
      exact ent_of_KO _ β g w.1 this
    by_cases hQ : ∃ w ∈ P, Q.under (𝓞 D.host.F) = w.under (𝓞 D.host.F)
    · obtain ⟨w, hw, hQw⟩ := hQ
      rcases GlobalTheory.IdemSupport.eq_or_eq_cP hQw with rfl | rfl
      · exact idem_smul_mem hβ (hA ⟨Q, hw⟩).1 hy
      · exact transfer hsd hU (fun y hy => idem_smul_mem hβ (hA ⟨w, hw⟩).2 hy) hy
    · push Not at hQ
      have := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hB' Q) hQ)
      exact idem_smul_mem hβ (ent_of_KO _ β g Q this).1 hy
  ext x
  constructor
  · intro hx
    have hS : x ∈ St β := (GlobalTheory.LevSplit.mem_St_iff β Λ hβ x).2
      ⟨fun y hy => mem_hat_of_idem hsd.1.fg fun Q => key x hx Q y hy,
        fun y hy => mem_hat_of_idem hsd.1.fg fun Q => key x⁻¹ (inv_mem hx) Q y hy⟩
    obtain ⟨h1, h2⟩ := (GlobalTheory.LevSplit.mem_St_iff β Λ hβ x).1 hS
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2, ?_⟩
    intro y
    refine ⟨fun hy => h1 y hy, fun hy => ?_⟩
    have := h2 _ hy
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec] at this
    exact this
  · intro hx
    obtain ⟨hU, hst⟩ := Subgroup.mem_inf.1 hx
    have hS : x ∈ St β := (GlobalTheory.LevSplit.mem_St_iff β Λ hβ x).2
      ⟨fun y hy => (hst y).1 hy, fun y hy => (hst _).2 (by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]; exact hy)⟩
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => ?_,
      Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun _ => ?_⟩, hU⟩
    · rw [Subgroup.mem_comap, hK]
      exact KO_of_St _ β w.1 hS
    · rw [Subgroup.mem_comap]
      exact KO_of_St _ β w' hS

end GlobalTheory.FunObj.LevRowSucc

namespace GlobalTheory.FunObj.GridChoice

open GlobalTheory.FunObj.LevRowSucc

theorem levRow_succ_inf_UA {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
    (S : GridChoice W U) (t : T) (i : ℕ) (h : i + 1 ≤ D.R.m) :
    S.levRow t (i + 1) h ⊓ UA D.sp.cm (G.V (.grid (i + 1) D.R.m)).gram = G.levMax (.grid (i + 1) D.R.m) := by
  have hm : D.R.m ≠ 0 := by have := D.R.two_le_m; omega
  rw [GridData.levMax]
  exact prodLev_inf_UA (S.B.isFrame (i + 1) D.R.m (by omega) h le_rfl)
    (G.isV (X := .grid (i + 1) D.R.m) ⟨h, le_rfl⟩ fun j e => by cases e).sd (locPl G t) _ _
    fun w => givenLevel_succ G t w.1 i D.R.m hm

end GlobalTheory.FunObj.GridChoice
end
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_eventuallyEq_pull {α : A.Fld} (hα : A.IsForm α) (x x' : A.Pt) (h : x.pt = x'.pt) :
    A.loc α x.1.1 =ᶠ[𝓝 x.crd] fun y => pull (fderiv ℂ (x'.ch ∘ x.ch.symm) y) (A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) y)) := by
  have hU : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
    x.ch.isOpen_inter_preimage_symm x'.ch.open_source
  have hxU : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source :=
    ⟨x.ch.map_source x.2, by simp only [Set.mem_preimage, x.ch.left_inv x.2, h]; exact x'.2⟩
  refine Filter.eventually_of_mem (hU.mem_nhds hxU) fun y hy => ?_
  show A.loc α x.1.1 y = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) y) (A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) y))
  let p : A.Pt := ⟨(x.1.1, x.ch.symm y), x.ch.map_target hy.1⟩
  let p' : A.Pt := ⟨(x'.1.1, x.ch.symm y), hy.2⟩
  have e1 : A.loc α x.1.1 y = α p := by rw [HolAtlas.loc, dite_eq_left hy.1]
  have e2 : A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) y) = α p' := A.loc_crd α p'
  have e3 : p.crd = y := x.ch.right_inv hy.1
  rw [e1, e2, hα.compat p p' rfl]
  show pull (fderiv ℂ (x'.ch ∘ x.ch.symm) p.crd) (α p') = _
  rw [e3]

theorem chg_facts (x x' : A.Pt) (h : x.pt = x'.pt) :
    IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) ∧ x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source ∧
    DifferentiableOn ℂ (x'.ch ∘ x.ch.symm) (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) ∧
    (x'.ch ∘ x.ch.symm) x.crd = x'.crd :=
  ⟨x.ch.isOpen_inter_preimage_symm x'.ch.open_source,
    ⟨x.ch.map_source x.2, by simp only [Set.mem_preimage, x.ch.left_inv x.2, h]; exact x'.2⟩,
    A.holo x.1.1 x'.1.1, by simp only [Function.comp_apply, x.ch.left_inv x.2, h]⟩

theorem loc_diffAt {α : A.Fld} (hα : A.IsForm α) (x : A.Pt) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α x.1.1 y) S) x.crd :=
  ((hα.smooth x.1.1 S).contDiffAt (x.ch.open_target.mem_nhds (x.ch.map_source x.2))).differentiableAt (by simp)

theorem isForm_del_dbar {α : A.Fld} (hα : A.IsForm α) : A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) := by
  have hloc : ∀ (T : (V n → Alt n) → V n → Alt n) (i : A.ι) (v : V n), v ∈ (A.e i).target →
      A.loc (fun x => T (A.loc α x.1.1) x.crd) i v = T (A.loc α i) v := by
    intro T i v hv
    rw [HolAtlas.loc, dite_eq_left hv]
    show T (A.loc α i) ((A.e i) ((A.e i).symm v)) = _
    rw [(A.e i).right_inv hv]
  refine ⟨⟨fun i S => ?_, fun x x' h => ?_⟩, ⟨fun i S => ?_, fun x x' h => ?_⟩⟩
  · exact ((GlobalTheory.T.contDiffOn_coefficients_delOperator_dbarOperator n _ (A.loc α i) (A.e i).open_target (hα.smooth i) S).1).congr fun v hv => by
      rw [show A.del α = fun x => delAt (A.loc α x.1.1) x.crd from rfl, hloc delAt i v hv]
  · obtain ⟨hU, hxU, hτ, hτx⟩ := chg_facts A x x' h
    have hβ : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α x'.1.1 y) S) ((x'.ch ∘ x.ch.symm) x.crd) := by
      rw [hτx]; exact loc_diffAt A hα x'
    show delAt (A.loc α x.1.1) x.crd = pull _ (delAt (A.loc α x'.1.1) x'.crd)
    rw [((GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local n x.crd).2.2.2.1 _ _ (loc_eventuallyEq_pull A hα x x' h)).1,
      (GlobalTheory.T.del_dbar_chainRule_holomorphicPullback n n _ _ _ x.crd hU hxU hτ hβ).1, hτx]
  · exact ((GlobalTheory.T.contDiffOn_coefficients_delOperator_dbarOperator n _ (A.loc α i) (A.e i).open_target (hα.smooth i) S).2).congr fun v hv => by
      rw [show A.dbar α = fun x => dbarAt (A.loc α x.1.1) x.crd from rfl, hloc dbarAt i v hv]
  · obtain ⟨hU, hxU, hτ, hτx⟩ := chg_facts A x x' h
    have hβ : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α x'.1.1 y) S) ((x'.ch ∘ x.ch.symm) x.crd) := by
      rw [hτx]; exact loc_diffAt A hα x'
    show dbarAt (A.loc α x.1.1) x.crd = pull _ (dbarAt (A.loc α x'.1.1) x'.crd)
    rw [((GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local n x.crd).2.2.2.1 _ _ (loc_eventuallyEq_pull A hα x x' h)).2,
      (GlobalTheory.T.del_dbar_chainRule_holomorphicPullback n n _ _ _ x.crd hU hxU hτ hβ).2, hτx]

end GlobalTheory.CxForm.HolAtlas

theorem GlobalTheory.CxForm.isForm_del_dbar : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (α : A.Fld), A.IsForm α →
    A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) :=
  fun _ _ _ A _ hα => A.isForm_del_dbar hα
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitPlaceExists

theorem exists_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    ∃ w : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w := by
  intro E _ _ _
  obtain ⟨p, hp, hsplit⟩ := GlobalTheory.SplitRealPrime.exists_prime_isSplitAt E

  have hP : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible

  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E)
    (Ideal.span {(p : ℤ)}) (by
      intro x hx
      rw [RingHom.mem_ker] at hx
      have : x = 0 := (FaithfulSMul.algebraMap_injective ℤ (𝓞 E)) (by rw [hx, map_zero])
      rw [this]
      exact Ideal.zero_mem _)
  have hpQ : ((p : ℕ) : 𝓞 E) ∈ Q := by
    have h1 : ((p : ℤ)) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
      change (p : ℤ) ∈ Ideal.under ℤ Q
      rw [hQ]
      exact Ideal.subset_span rfl
    rw [Ideal.mem_comap] at h1
    simpa using h1

  have hQ0 : Q ≠ ⊥ := Ideal.IsMaximal.ne_bot_of_isIntegral_int Q
  exact ⟨⟨Q, hQmax.isPrime, hQ0⟩, hsplit _ hpQ⟩

end GlobalTheory.SplitPlaceExists
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.definiteForm_stabilizer_finite_away_from_p : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (K' : Subgroup (Gr G 1)),
  Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ (B : GlobalTheory.LKDef.DForm G) (x : G.GAf × Gr G 1),
    Finite (GlobalTheory.LKLoc.locPart B.emb.range (L.K.toSubgroup.prod K') x) := by
  first | (exact @GlobalTheory.DefStab.finite_locPart) | (exact GlobalTheory.DefStab.finite_locPart) | (intros; apply GlobalTheory.DefStab.finite_locPart  <;> assumption)
end
