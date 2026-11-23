module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle089
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle044
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle090
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle088
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Formalism.GaussJetBounds.Bundle003
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle003
public import Formalism.LocalToGlobal.Columns.Adelic
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle091
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLatticeSesquilinearFormIsHerm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.LocalRingCardinality.Params
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.crystalline_hodgeTateMultiplicity_ne_zero_of_jump : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL), Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → ∀ τ u, IsJumpV (P.PD K) T.ρ τ u → multV (P.PD K) T.ρ τ u ≠ 0 := by
  first | exact @GlobalTheory.HTW.Rec.jump_multV_ne_zero | exact GlobalTheory.HTW.Rec.jump_multV_ne_zero | (intros; apply GlobalTheory.HTW.Rec.jump_multV_ne_zero <;> assumption)
end

section

open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

theorem _root_.GlobalTheory.T.isParahoricTypeVector_of_blockTypeVector_padic_iso : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ (ξ : Fˣ →* ℂˣ) (χ : (ZMod g)ˣ →* ℂˣ), TamePart (ξ.comp (Units.map e.toMonoidHom)) χ → ∀ (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin (r + t)) F) V) (u : V), GlobalTheory.SplitRead.IsBlockVec ξ ρ u → IsParVec (ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) r t χ u := by
  first | exact @GlobalTheory.ParRead.isParVec_of_isBlockVec | exact GlobalTheory.ParRead.isParVec_of_isBlockVec | (intros; apply GlobalTheory.ParRead.isParVec_of_isBlockVec <;> assumption)
end

section

open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

theorem _root_.GlobalTheory.T.isIrreducibleSmooth_pullback_padic_ringIso : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ (n : ℕ) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) F)), IrrSm (Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) : QRep g n) := by
  first | exact @GlobalTheory.SerSys.irrSm_pullback | exact GlobalTheory.SerSys.irrSm_pullback | (intros; apply GlobalTheory.SerSys.irrSm_pullback <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

theorem window_and_cTB_of_jumps_at_embeddings :
    ∀ (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (h r n t : ℕ) [CharZero S.Qp] [FiniteDimensional S.Qp S.K], S.W.s = 1 → Nat.card (S.K →ₐ[S.Qp] S.LL) = finrank S.Qp S.K → finrank S.Qp S.K ≤ n → LocalSituation.gK S = 0 → LocalSituation.vdegMs S (LocalSituation.mN (LocalSituation.ell S) 1 (h + h)) = LocalSituation.mN (LocalSituation.ell S) 1 (h + h) - 1 → t ≤ h → (∀ τ : S.K →ₐ[S.Qp] S.LL, ∃ U : Finset ℤ, U.card ≤ r ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u + 1 ≤ h) ∧ ∀ a, IsJumpV S.PD Y.ρ τ a → a ∈ U) → (∀ a ∈ LocalSituation.Jset S Y, -(h : ℤ) ≤ a ∧ a ≤ h) ∧ ∀ e < t, LocalSituation.cTBY S Y h h e ≤ cBnum (LocalSituation.ell S) h t (n * r) := by
  intro S Y h r n t _ _ hs hcard hn hg hv hth hU
  classical
  choose U hUc hUb hUj using hU
  have hpos : 0 < finrank S.Qp S.K := finrank_pos
  have hfin : Finite (S.K →ₐ[S.Qp] S.LL) := Nat.finite_of_card_ne_zero (by omega)
  letI : Fintype (S.K →ₐ[S.Qp] S.LL) := Fintype.ofFinite _
  have hsub : LocalSituation.Jset S Y ⊆ ((Finset.univ.biUnion U : Finset ℤ) : Set ℤ) := by
    intro a ha
    obtain ⟨τ, hτ⟩ := jump_of_total S.PD Y.ρ hcard a ha
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨τ, Finset.mem_univ _, hUj τ a hτ⟩)
  have hb : ∀ u ∈ Finset.univ.biUnion U, -(h : ℤ) ≤ u ∧ u + 1 ≤ h := by
    intro u hu
    obtain ⟨τ, -, hτ⟩ := Finset.mem_biUnion.1 hu
    exact hUb τ u hτ
  have hc : (Finset.univ.biUnion U).card ≤ n * r := by
    refine (Finset.card_biUnion_le_card_mul _ _ r fun τ _ => hUc τ).trans (Nat.mul_le_mul_right _ ?_)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
    exact hn
  refine ⟨fun a ha => ?_, fun e he => ?_⟩
  · have := hb a (Finset.mem_coe.1 (hsub ha))
    omega
  · unfold LocalSituation.cTBY
    rw [hg, hs, hv]
    exact cTB_le (LocalSituation.ell S) h t (n * r) e S.PD.hp _ _ hsub hc hb he hth

end GlobalTheory.HubLoc
end

section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

noncomputable section

namespace GlobalTheory.StdBaseChange

def pureSet (K : Type) [CommRing K] {S : Type} [Fintype S] {k n : ℕ}
    (A : S → Set (MvPolynomial (Fin k × Fin n) K)) : Set (MvPolynomial (S × (Fin k × Fin n)) K) :=
  {P | ∃ F : S → MvPolynomial (Fin k × Fin n) K, (∀ s, F s ∈ A s) ∧ P = ∏ s, blockEmb K s (F s)}

theorem tensorLat_span (R K : Type) [CommRing R] [CommRing K] [Algebra R K] {S : Type} [Fintype S] {k n : ℕ}
    (A : S → Set (MvPolynomial (Fin k × Fin n) K)) :
    tensorLat R K (fun s => Submodule.span R (A s)) = Submodule.span R (pureSet K A) := by
  classical
  apply le_antisymm
  · unfold tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    have h1 : ∀ s, blockEmb K s (F s) ∈ Submodule.span R (blockEmb K s '' A s) := fun s =>
      Submodule.apply_mem_span_image_of_mem_span ((blockEmb K s).toLinearMap.restrictScalars R) (hF s)
    have h2 : ∀ t : Finset S, ∏ s ∈ t, blockEmb K s (F s) ∈ ∏ s ∈ t, Submodule.span R (blockEmb K s '' A s) := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
        rw [Finset.prod_empty, Finset.prod_empty]
        exact Submodule.one_le.mp le_rfl
      | insert a t ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha]
        exact Submodule.mul_mem_mul (h1 a) ih
    have h3 := h2 Finset.univ
    rw [Submodule.prod_span] at h3
    refine Submodule.span_mono ?_ h3
    intro P hP
    obtain ⟨G, hG, rfl⟩ := (Set.mem_fintype_prod _ _).mp hP
    choose F' hF' hFG using hG
    exact ⟨F', hF', by simp only [hFG]⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, fun s => Submodule.subset_span (hF s), rfl⟩

theorem image_pureSet {K L : Type} [CommRing K] [CommRing L] (φ : K →+* L) {S : Type} [Fintype S] {k n : ℕ}
    (A : S → Set (MvPolynomial (Fin k × Fin n) K)) :
    MvPolynomial.map φ '' pureSet K A = pureSet L fun s => MvPolynomial.map φ '' A s := by
  have h : ∀ F : S → MvPolynomial (Fin k × Fin n) K,
      MvPolynomial.map φ (∏ s, blockEmb K s (F s)) = ∏ s, blockEmb L s (MvPolynomial.map φ (F s)) := by
    intro F
    rw [map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [blockEmb, map_rename]
  ext P
  constructor
  · rintro ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    exact ⟨_, fun s => ⟨F s, hF s, rfl⟩, h F⟩
  · rintro ⟨G, hG, rfl⟩
    choose F hF hFG using hG
    exact ⟨_, ⟨F, hF, rfl⟩, by rw [h]; simp only [hFG]⟩

theorem span_map_span {R K O L σ : Type} [CommRing R] [CommRing K] [Algebra R K] [CommRing O] [CommRing L] [Algebra O L]
    (φ : K →+* L) (ψ : R →+* O) (h : ∀ r, algebraMap O L (ψ r) = φ (algebraMap R K r)) (T : Set (MvPolynomial σ K)) :
    Submodule.span O (MvPolynomial.map φ '' (Submodule.span R T : Set (MvPolynomial σ K))) =
      Submodule.span O (MvPolynomial.map φ '' T) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul a y _ hy =>
      have e : MvPolynomial.map φ (a • y) = ψ a • MvPolynomial.map φ y := by
        rw [← algebraMap_smul K a y, ← algebraMap_smul L (ψ a), smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C, h]
      rw [e]
      exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem dualWeyl_map (R K : Type) [CommRing R] [IsDomain R] [CommRing K] [Algebra R K] (n : ℕ) (ν : Fin n → ℕ) :
    (dualWeyl R n n ν).map (mapAlgHom (Algebra.ofId R K)).toLinearMap = Submodule.span R (StdDual.bidSet K n ν) := by
  rw [StdDual.dualWeyl_eq, Submodule.map_span, ← StdDual.image_bidSet (algebraMap R K)]
  rfl

theorem weyl_map (R K : Type) [CommRing R] [CommRing K] [Algebra R K] (n : ℕ) (ν : Fin n → ℕ) :
    (weyl R n n le_rfl ν).map (mapAlgHom (Algebra.ofId R K)).toLinearMap = Submodule.span R (StdDual.wordSet K n ν) := by
  rw [StdDual.weyl_eq, Submodule.map_span, ← StdDual.image_wordSet (algebraMap R K)]
  rfl

theorem std_baseChange : ∀ (O Kf K ι : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [Field K] [NumberField K] [Fintype ι] (eK : K →+* Kf) (ψ : 𝓞 K →+* O), (∀ r, algebraMap O Kf (ψ r) = eK r) → ∀ (n : ℕ) (lam : ι → DomWeight n), Submodule.span O (MvPolynomial.map eK '' (nabStd K lam : Set (Pol K ι n))) = (tensorLat O Kf fun τ => stdN O Kf n (lam τ).natW) ∧ Submodule.span O (MvPolynomial.map eK '' (delStd K lam : Set (Pol K ι n))) = (tensorLat O Kf fun τ => stdD O Kf n (lam τ).natW) := by
  intro O Kf K ι _ _ _ _ _ _ _ eK ψ h n lam
  constructor
  · have e : nabStd K lam = tensorLat (𝓞 K) K fun τ => Submodule.span (𝓞 K) (StdDual.bidSet K n (lam τ).natW) := by
      unfold nabStd
      congr 1
      funext τ
      exact dualWeyl_map (𝓞 K) K n (lam τ).natW
    rw [e, tensorLat_span, span_map_span eK ψ h, image_pureSet]
    simp only [stdN, dualWeyl_map, StdDual.image_bidSet]
    rw [tensorLat_span]
  · have e : delStd K lam = tensorLat (𝓞 K) K fun τ => Submodule.span (𝓞 K) (StdDual.wordSet K n (lam τ).natW) := by
      unfold delStd
      congr 1
      funext τ
      exact weyl_map (𝓞 K) K n (lam τ).natW
    rw [e, tensorLat_span, span_map_span eK ψ h, image_pureSet]
    simp only [stdD, weyl_map, StdDual.image_wordSet]
    rw [tensorLat_span]

end GlobalTheory.StdBaseChange
end
end

section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

theorem _root_.GlobalTheory.T.exists_cofactorTwist_dualWeyl : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∀ f ∈ dualWeyl R (m + 1) (m + 1) ν, ∃ g ∈ dualWeyl R (m + 1) (m + 1) (nuDual ν), CofRel R m ν f g := by
  first | exact @GlobalTheory.ValCmp.exists_cofRel_dualWeyl | exact GlobalTheory.ValCmp.exists_cofRel_dualWeyl | (intros; apply GlobalTheory.ValCmp.exists_cofRel_dualWeyl <;> assumption)
end

section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

theorem _root_.GlobalTheory.T.exists_cofactorTwist_highestWeight : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∃ g ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν), CofRel R m ν (hw R le_rfl ν) g := by
  first | exact @GlobalTheory.ValCmp.exists_cofRel_hw | exact GlobalTheory.ValCmp.exists_cofRel_hw | (intros; apply GlobalTheory.ValCmp.exists_cofRel_hw <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG

noncomputable section

namespace GlobalTheory.DiagElem

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) :
    x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem mem_std {n : ℕ} (x : Fin n → w.adicCompletion E) :
    x ∈ (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ↔
      ∀ i, Valued.v (x i) ≤ 1 := by
  constructor
  · intro hx
    refine Submodule.span_induction (p := fun x _ => ∀ i, Valued.v (x i) ≤ 1) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, rfl⟩ i
      by_cases h : i = j
      · subst h; simp
      · simp [Pi.single_apply, h]
    · intro i; simp
    · intro a b _ _ ha hb i
      simpa using (Valued.v.map_add (a i) (b i)).trans (max_le (ha i) (hb i))
    · intro c a _ ha i
      have hc : Valued.v (c : w.adicCompletion E) ≤ 1 := c.2
      show Valued.v ((c : w.adicCompletion E) * a i) ≤ 1
      rw [map_mul]
      exact mul_le_one' hc (ha i)
  · intro hx
    have e : x = ∑ i, (⟨x i, hx i⟩ : w.adicCompletionIntegers E) • Pi.basisFun (w.adicCompletion E) (Fin n) i := by
      ext j
      rw [Finset.sum_apply, Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb]) (by simp)]
      simp only [Pi.basisFun_apply, Pi.smul_apply, Pi.single_eq_same]
      rw [Algebra.smul_def]
      simp
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def dEnt {n : ℕ} (ϖ : w.adicCompletion E) (S : Finset (Fin n)) (i : Fin n) : w.adicCompletion E :=
  if i ∈ S then ϖ else 1

theorem mem_glMap_diag {n : ℕ} {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (S : Finset (Fin n))
    (d : GL (Fin n) (w.adicCompletion E))
    (hd : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (dEnt w ϖ S))
    (x : Fin n → w.adicCompletion E) :
    x ∈ glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ↔
      ∀ i, Valued.v (x i) ≤ Valued.v (dEnt w ϖ S i) := by
  have hϖ0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  have hf0 : ∀ i, dEnt w ϖ S i ≠ 0 := fun i => by unfold dEnt; split_ifs <;> simp [hϖ0]
  simp only [glMap, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.toLin'_apply, hd,
    Matrix.mulVec_diagonal, mem_std]
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    rw [Matrix.mulVec_diagonal, map_mul]
    exact mul_le_of_le_one_right' (hy i)
  · intro hx
    refine ⟨fun i => x i / dEnt w ϖ S i, fun i => ?_, ?_⟩
    · rw [map_div₀]
      exact div_le_one_of_le₀ (hx i) zero_le
    · funext i
      rw [Matrix.mulVec_diagonal, mul_div_cancel₀ _ (hf0 i)]

end GlobalTheory.DiagElem

namespace GlobalTheory.DiagElem

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

def redS {n : ℕ} (S : Finset (Fin n)) :
    (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 →ₗ[w.adicCompletionIntegers E]
      (S → IsLocalRing.ResidueField (w.adicCompletionIntegers E)) where
  toFun x i := IsLocalRing.residue _ ⟨x.1 i, (mem_std w x.1).1 x.2 i⟩
  map_add' x y := by
    funext i
    rw [Pi.add_apply, ← map_add (f := _)]
    rfl
  map_smul' c x := by
    funext i
    rw [Pi.smul_apply, RingHom.id_apply, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq,
      ← map_mul]
    congr 1

theorem redS_surjective {n : ℕ} (S : Finset (Fin n)) : Function.Surjective (redS w S) := by
  intro c
  choose a ha using fun i : S => IsLocalRing.residue_surjective (c i)
  refine ⟨⟨fun j => if h : j ∈ S then (a ⟨j, h⟩ : w.adicCompletion E) else 0,
    (mem_std w _).2 fun j => ?_⟩, ?_⟩
  · split_ifs
    · exact (a _).2
    · simp
  · funext ⟨i, hi⟩
    change IsLocalRing.residue _ _ = _
    rw [← ha]
    congr 1
    ext
    simp [hi]

theorem glMap_diag_mem_subElem :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
      (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ →
      ∀ (S : Finset (Fin n)) (d : GL (Fin n) (w.adicCompletion E)),
        (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
          Matrix.diagonal (fun i => if i ∈ S then ϖ else 1) →
        (haveI := GlobalTheory.RowSatakeBound.finite_residue w
         glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈
           Subtype.val '' subElem S.card (std (w.adicCompletionIntegers E) (w.adicCompletion E) n)) := by
  intro E _ _ w n ϖ hϖ S d hd
  have hd' : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (dEnt w ϖ S) := hd
  have hϖle : Valued.v ϖ ≤ WithZero.exp (-1 : ℤ) := hϖ.le
  have hexp : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  refine ⟨⟨_, glMap_isLattice d (std _ _ n)⟩, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
  · intro x hx
    rw [mem_glMap_diag w hϖ S d hd' x] at hx
    rw [mem_std]
    intro i
    refine (hx i).trans ?_
    unfold dEnt
    split_ifs
    · exact hϖle.trans hexp.le
    · simp
  · have hk : (glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1).comap
        (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1.subtype =
        LinearMap.ker (redS w S) := by
      ext x
      rw [Submodule.mem_comap, Submodule.subtype_apply, mem_glMap_diag w hϖ S d hd',
        LinearMap.mem_ker]
      have hx := (mem_std w x.1).1 x.2
      constructor
      · intro h
        funext ⟨i, hi⟩
        change IsLocalRing.residue _ _ = 0
        rw [IsLocalRing.residue_eq_zero_iff]
        apply Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr
        have := h i
        unfold dEnt at this
        rw [if_pos hi] at this
        exact lt_of_le_of_lt (this.trans hϖle) hexp
      · intro h i
        unfold dEnt
        split_ifs with hi
        · have := congrFun h ⟨i, hi⟩
          change IsLocalRing.residue _ _ = 0 at this
          rw [IsLocalRing.residue_eq_zero_iff] at this
          rw [hϖ]
          exact le_exp_neg_one_of_lt_one (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp this)
        · rw [map_one]; exact hx i
    change Nat.card ((std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ⧸
      (glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1).comap
        (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1.subtype) = _
    rw [hk, Nat.card_congr (LinearMap.quotKerEquivOfSurjective _ (redS_surjective w S)).toEquiv,
      Nat.card_fun, Nat.card_eq_fintype_card (α := S), Fintype.card_coe]
    rfl
  · rw [Submodule.smul_le]
    intro r hr x hx
    rw [mem_glMap_diag w hϖ S d hd']
    rw [mem_std] at hx
    have hr1 : Valued.v (r : w.adicCompletion E) < 1 :=
      Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hr
    intro i
    have hri : Valued.v ((r • x) i) < 1 := by
      change Valued.v ((r : w.adicCompletion E) * x i) < 1
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (hx i)) hr1
    unfold dEnt
    split_ifs
    · rw [hϖ]; exact le_exp_neg_one_of_lt_one hri
    · rw [map_one]; exact hri.le

end GlobalTheory.DiagElem
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

theorem _root_.GlobalTheory.T.latticeJetsIntegral_iff_integralFrames : ∀ (D : D7) (N N' : ℕ) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (Yl : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (JetsInt D lm Yl F ↔ ∀ (n : ℕ) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, y j ∈ Yl) → JetsIntegral (atLin (fun k j => tauEmb D lm k.1 (y j k.2.1 k.2.2)) (fun j => MvPowerSeries.X j) F)) ∧ (JetsInt D lm Yl F → ∀ (ν : Type) [Fintype ν] (M : D.what₂.Tau × Fin N' × Fin N → ν → ℂ_[p]), (∀ x, ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, y j ∈ Yl) ∧ ∀ k, M k x = ∑ j, r j * tauEmb D lm k.1 (y j k.2.1 k.2.2)) → JetsIntegral (atLin M (fun j => MvPowerSeries.X j) F)) := by
  first | exact @GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames.jetsInt_frames | exact GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames.jetsInt_frames | (intros; apply GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames.jetsInt_frames <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory.HostKur

theorem host_image_mem_Kur : ∀ {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime], l ∉ H.small → l ≠ H.q → l ≠ H.d →
    ∀ (c : H.E →+* PadicAlgCl l) (x : H.E), c x ∈ Loc.MaximalUnramifiedExtension l := by
  intro R H l _ hl2 hq hd c x
  exact GlobalTheory.HubLoc.image_mem_Kur H c (UpperTheory.Small.not_dvd_condN H Fact.out hl2 hq hd) x

end GlobalTheory.HostKur
end

section

open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Col
open scoped TensorProduct

theorem _root_.GlobalTheory.T.integralAt_of_adelic_integralAt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (P : HeightOneSpectrum (𝓞 E)) (x : E), IntAtA (F := F) P (iA F E x) → IntAt P x := by
  first | exact @GlobalTheory.RatInt.intAt_of_intAtA | exact GlobalTheory.RatInt.intAt_of_intAtA | (intros; apply GlobalTheory.RatInt.intAt_of_intAtA <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators ComplexConjugate

namespace GlobalTheory.JetsGenusOne

theorem sgStar_eq (L : PeriodPair) : TaylorLogMetric.sgStar L.lattice.toAddSubgroup = Formalism.L2.Th1.F.sgStar L := by
  rw [GlobalTheory.OddTheta.sgStar_eq L _ (fun _ => Iff.rfl), GlobalTheory.Mem.Col2.ThetaVec.sgStar_eq]

end GlobalTheory.JetsGenusOne

namespace GlobalTheory.JetsGenusOne

end GlobalTheory.JetsGenusOne
end
