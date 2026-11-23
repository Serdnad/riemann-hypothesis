module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardAdditiveCharacterLocalNeOneSplitPrime
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle278
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle286
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle119
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle287
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitive
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle238
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle143
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle257
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle259
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle112
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerRepK
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle288
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideUnfolding
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorIntegralModIntegralPointsLe
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle289
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianDoubleCoset_kernel_bound_by_weight : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ‖∑ᶠ y : {y // S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * S.om d y‖ ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  first | exact @GlobalTheory.HL.KernelWeight.kernel_weight | exact GlobalTheory.HL.KernelWeight.kernel_weight | (intros; apply GlobalTheory.HL.KernelWeight.kernel_weight <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.hermitianLattice_level_local_dual_quotient_length_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → (loc v L).toAddSubgroup.relIndex (loc v (_root_.GlobalTheory.St.G.dualL cm.sig J L)).toAddSubgroup = T ^ 2 ∧ ∃ d ∈ loc v (_root_.GlobalTheory.St.G.dualL cm.sig J L), ∀ x ∈ loc v (_root_.GlobalTheory.St.G.dualL cm.sig J L), ∃ a ∈ intV E v, x - a • d ∈ loc v L :=
  @_root_.GlobalTheory.St.G.tLat_local_index
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.standardAdditiveCharacter_local_ne_one_splitPrime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (psi : E ⊗[F] Ad F → ℂ), (∀ x y, psi (x + y) = psi x * psi y) → (∀ x ∈ OAd F E, psi x = 1) → (∀ x : E, psi (inclE (F := F) (Ad F) x) * Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ E x : ℚ) : ℂ)) = 1) → ∀ (p : ℕ), p.Prime → SplitsIn E p → ∀ (v : HeightOneSpectrum (𝓞 F)), (p : 𝓞 F) ∈ v.asIdeal → ∀ e ∈ intV E v, e * e = e → e ≠ 0 → ∃ a ∈ intV E v, psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((p : F)⁻¹) * (e * a))) ≠ 1 := by
  first | exact @GlobalTheory.St.G.psi_local_ne_one | exact GlobalTheory.St.G.psi_local_ne_one | (intros; apply GlobalTheory.St.G.psi_local_ne_one <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.Weight

theorem invVol_three {G : Type} [Group G] (R M Z A B : Subgroup G) (hM : M ≤ R) (hZ : Z ≤ M) (hA : A ≤ R) (hB : B ≤ R)
    (nM : ∀ s ∈ R, ∀ t ∈ M, s * t * s⁻¹ ∈ M) (nZ : ∀ s ∈ R, ∀ t ∈ Z, s * t * s⁻¹ ∈ Z)
    (h1 : A.relIndex B ≠ 0) (h2 : B.relIndex A ≠ 0)
    (h3 : (A ⊓ M).relIndex (B ⊓ M) ≠ 0) (h4 : (B ⊓ M).relIndex (A ⊓ M) ≠ 0) :
    GlobalTheory.HL.invVol A B = GlobalTheory.HL.invVol (A ⊓ Z) (B ⊓ Z) * GlobalTheory.HL.invVol ((A ⊓ M) ⊔ Z) ((B ⊓ M) ⊔ Z) *
      GlobalTheory.HL.invVol (A ⊔ M) (B ⊔ M) := by
  rw [(GlobalTheory.IndexProd.invVol_eq_inf_mul_sup_and_mono G R M A B hM hA hB nM h1 h2).1,
    (GlobalTheory.IndexProd.invVol_eq_inf_mul_sup_and_mono G M Z (A ⊓ M) (B ⊓ M) hZ inf_le_right inf_le_right
      (fun s hs t ht => nZ s (hM hs) t ht) h3 h4).1,
    inf_assoc, inf_assoc, inf_eq_right.mpr hZ]

theorem invVol_nonneg {G : Type} [Group G] (A B : Subgroup G) : 0 ≤ GlobalTheory.HL.invVol A B := by
  unfold GlobalTheory.HL.invVol
  positivity

theorem om_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → N.om Λ ≤ (N.bI Λ : ℝ) ^ Module.finrank K N.Wt * N.Del ^ r * (Ideal.absNorm 𝔠 : ℝ) ^ (2 * (3 * e + 11) * (2 * r + 1) ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hT 𝔠 hc hs hTd hD e hSp hNe
  obtain ⟨-, -, nM, nZ, hnil⟩ := GlobalTheory.UnipStab.common_unipotent_stabiliser K V H hK r N
  obtain ⟨-, -, -, -, hRef, -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hT
  obtain ⟨-, hg0, hi0, -, hgi, -⟩ := GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ hg hT
  have hTop := GlobalTheory.T.hermFramePairNormalForm_invVol_top_layer_le K V H hK r N g Λ hg hT 𝔠 hc hs hTd hD e hSp hNe
  have hBot := GlobalTheory.T.hermFramePairNormalForm_invVol_skew_layer_le K V H hK r N g Λ hg hT 𝔠 hc hs hTd hD e hSp hNe
  have hMid := GlobalTheory.T.haarInvVolume_middleLayer_eichler_le K V H hK r N g Λ hg hT hSp
  have hΛ : Submodule.IsFullLattice K Λ := by
    have h := hT.1.1.1
    unfold IsLatMod at h
    obtain ⟨⟨M, hM, hE⟩, hsp⟩ := h
    have hfg : Λ.FG := by
      rw [hE, rs, Submodule.restrictScalars_bot, sup_bot_eq]
      exact hM
    letI : Submodule.IsLattice K Λ := Submodule.IsLattice.of_fg K hfg
    exact ⟨hsp⟩
  have hRefFull : Submodule.IsFullLattice K (N.Ref (latL N.F N.F' Λ)) := by
    letI := hRef
    obtain ⟨_, _, hC, _, hWn, hUp, _, _, _, _, _, hPi⟩ :=
      GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
    have hspan : Submodule.span K (N.Ref (latL N.F N.F' Λ) : Set V) = ⊤ := by
      apply eq_top_iff.mpr
      rw [← hC.sup_eq_top]
      apply sup_le
      · intro w hw
        obtain ⟨c, hc, hcΛ⟩ := GlobalTheory.DegCnt.InnerLat.exists_mult hΛ.span_eq_top w
        have hwN : w ∈ N.Wn := by rw [hWn]; exact Submodule.mem_sup_left hw
        have hwU : w ∈ uPerp N.F N.F' := by rw [hUp]; exact Submodule.mem_sup_left hwN
        rw [← Submodule.smul_mem_iff _ hc]
        apply Submodule.subset_span
        exact Submodule.mem_sup_right ⟨⟨(uPerp N.F N.F').smul_mem c hwU,
          Submodule.mem_sup_left hcΛ⟩, N.Wn.smul_mem c hwN⟩
      · rw [hPi, ← GlobalTheory.DegCnt.InnerLat.span_hermFramePair_lattice_eq_sup N]
        exact Submodule.span_mono (show (N.P0 : Set V) ⊆ N.Ref (latL N.F N.F' Λ) from
          fun _ hx => Submodule.mem_sup_left hx)
    exact ⟨hspan⟩
  have hR1 : N.R1 ≤ N.R := inf_le_left
  have hZ : N.ZI ≤ N.R1 := inf_le_left
  have key : ∀ L : Submodule (𝓞 K) V, N.Gam L ⊓ N.R1 = N.R1 ⊓ MulAction.stabilizer (V ≃ₗ[K] V) L := by
    intro L
    unfold NF.Gam
    rw [inf_right_comm, inf_eq_right.mpr hR1]
  have hnil1 : ∀ s ∈ N.R1, ((s : V →ₗ[K] V) - 1) ^ (2 * r + 1) = 0 := fun s hs => hnil s (hR1 hs)
  have h3 := (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R1 _ hnil1 _ _ hRefFull hΛ).1
  have h4 := (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R1 _ hnil1 _ _ hΛ hRefFull).1
  rw [← key, ← key] at h3 h4
  have hprod := invVol_three N.R N.R1 N.ZI (N.Gam (N.Ref (latL N.F N.F' Λ))) (N.Gam Λ) hR1 hZ inf_le_left inf_le_left
    nM nZ (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R _ hnil _ _ hRefFull hΛ).1
    (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R _ hnil _ _ hΛ hRefFull).1 h3 h4
  have h1 : (1 : ℝ) ≤ (N.gI g Λ : ℝ) * N.iI g Λ := by
    have : 1 ≤ N.gI g Λ * N.iI g Λ := Nat.mul_pos hg0 hi0
    exact_mod_cast this
  have hpow : ((N.gI g Λ : ℝ) * N.iI g Λ) ^ (r - N.j) ≤ N.Del ^ r :=
    (pow_le_pow_right₀ h1 (Nat.sub_le _ _)).trans (pow_le_pow_left₀ (by linarith) hgi r)
  have hMid' := hMid.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  have hDel : (0 : ℝ) ≤ N.Del := by linarith
  unfold NF.om
  rw [hprod]
  calc _ ≤ (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) *
        ((N.bI Λ : ℝ) ^ Module.finrank K N.Wt * N.Del ^ r) *
        (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) :=
        mul_le_mul (mul_le_mul hBot hMid' (invVol_nonneg _ _) (by positivity)) hTop (invVol_nonneg _ _) (by positivity)
    _ = _ := by rw [mul_assoc 2, two_mul ((3 * e + 11) * _), pow_add]; ring

end GlobalTheory.DegCnt.Weight
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.SmoothKType


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem exists_garding_kMap (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H)
    (hσ : IsURepOn (UJset ε) σ) (hK : IsKTypeOf ε σ μ S) :
    ∃ (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (T : S →ₗ[ℂ] H), SmoothOnG ε α ∧
      HasCompactSupport (fun g : UJ ε => α (umat g)) ∧
      (∀ (s : S) (u : H), ⟪u, T s⟫_ℂ = ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε)) ∧
      (∀ k ∈ Kset ε, ∀ x y : S, (y : H) = σ k x → T y = σ k (T x)) ∧ T ≠ 0 := by
  have : (muG ε).IsMulRightInvariant := ⟨fun g => indefinite_unitary_unimodular n ε g⟩
  obtain ⟨v, hvS, hv0, -⟩ := hK.2.2.2.1
  have humat : Continuous (fun g : UJ ε => umat g) := (isClosedEmbeddingMatrix n ε).1.continuous
  have hcont : ∀ s : H, Continuous (fun g : UJ ε => σ (umat g) s) := fun s =>
    (hσ.2.2 s).comp_continuous humat (fun g => g.2)
  have hre : Continuous (fun g : UJ ε => (⟪v, σ (umat g) v⟫_ℂ).re) :=
    Complex.continuous_re.comp (continuous_const.inner (hcont v))
  have hone : 0 < (⟪v, σ (umat (1 : UJ ε)) v⟫_ℂ).re := by
    have : σ (umat (1 : UJ ε)) = 1 := hσ.1.1
    rw [this]
    exact re_inner_self_pos (𝕜 := ℂ).2 hv0
  obtain ⟨a, ha, ha0, ha1, hac, haU, haK⟩ := exists_conjInvariant_bump n ε
    {g | 0 < (⟪v, σ (umat g) v⟫_ℂ).re} ((isOpen_lt continuous_const hre).mem_nhds hone)
  have hacont : Continuous (fun g : UJ ε => a (umat g)) := ha.continuous.comp humat
  have hacC : Continuous (fun g : UJ ε => (a (umat g) : ℂ)) := Complex.continuous_ofReal.comp hacont
  have hsuppC : HasCompactSupport (fun g : UJ ε => (a (umat g) : ℂ)) :=
    hac.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  have hint : ∀ s : H, Integrable (fun g : UJ ε => (a (umat g) : ℂ) • σ (umat g) s) (muG ε) :=
    fun s => (hacC.smul (hcont s)).integrable_of_hasCompactSupport hsuppC.smul_right
  let T : S →ₗ[ℂ] H :=
    { toFun := fun s => ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε)
      map_add' := by
        intro s t
        rw [← integral_add (hint s) (hint t)]
        simp only [Submodule.coe_add, map_add (f := _), smul_add]
      map_smul' := by
        intro c s
        rw [RingHom.id_apply, ← integral_smul]
        simp only [Submodule.coe_smul, map_smul, smul_comm c] }
  have hT : ∀ (s : S) (u : H), ⟪u, T s⟫_ℂ =
      ∫ g : UJ ε, (a (umat g) : ℂ) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) := by
    intro s u
    show ⟪u, ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε)⟫_ℂ = _
    rw [← integral_inner (hint s)]
    simp only [inner_smul_right]
  refine ⟨fun y => (a y : ℂ), T, ?_, hsuppC, hT, ?_, ?_⟩
  · intro g₀ _
    refine ⟨Set.univ, fun y => (a y : ℂ), isOpen_univ, trivial, ?_, fun _ _ _ => rfl⟩
    exact (Complex.ofRealCLM.contDiff.comp ha).contDiffOn
  · intro k hk s s' hs'
    have hu : k ∈ Set.range (fun g : UJ ε => umat g) := by
      rw [(isClosedEmbeddingMatrix n ε).2]
      exact (maximal_compact_facts n ε).1 k hk
    obtain ⟨κ, rfl⟩ := hu
    show ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s' ∂(muG ε) =
      σ (umat κ) (∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε))
    rw [← ContinuousLinearMap.integral_comp_comm _ (hint s), hs']
    have e1 : ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) (σ (umat κ) s) ∂(muG ε) =
        ∫ g : UJ ε, (a (umat (g * κ⁻¹)) : ℂ) • σ (umat g) s ∂(muG ε) := by
      rw [← integral_mul_right_eq_self
        (fun g : UJ ε => (a (umat (g * κ⁻¹)) : ℂ) • σ (umat g) (s : H)) κ]
      congr 1
      funext g
      have : σ (umat (g * κ)) = _ := hσ.1.2 (umat g) g.2 (umat κ) κ.2
      rw [this, mul_inv_cancel_right]
      rfl
    have e2 : ∫ g : UJ ε, σ (umat κ) ((a (umat g) : ℂ) • σ (umat g) s) ∂(muG ε) =
        ∫ g : UJ ε, (a (umat (κ⁻¹ * g)) : ℂ) • σ (umat g) s ∂(muG ε) := by
      rw [← integral_mul_left_eq_self
        (fun g : UJ ε => (a (umat (κ⁻¹ * g)) : ℂ) • σ (umat g) (s : H)) κ]
      congr 1
      funext g
      have : σ (umat (κ * g)) = _ := hσ.1.2 (umat κ) κ.2 (umat g) g.2
      rw [this, inv_mul_cancel_left, map_smul]
      rfl
    refine e1.trans (Eq.trans ?_ e2.symm)
    congr 1
    funext g
    have hk' : umat κ⁻¹ ∈ Kset ε := (KG ε).inv_mem (x := κ) hk
    have : a (umat (κ⁻¹ * g)) = a (umat (g * κ⁻¹)) := haK _ hk' (umat g)
    rw [this]
  · intro h0
    have h1 := hT ⟨v, hvS⟩ v
    rw [h0, LinearMap.zero_apply, inner_zero_right] at h1
    have hi : Integrable (fun g : UJ ε => (a (umat g) : ℂ) * ⟪v, σ (umat g) v⟫_ℂ) (muG ε) :=
      (hacC.mul (continuous_const.inner (hcont v))).integrable_of_hasCompactSupport hsuppC.mul_right
    have h2 := congrArg Complex.re h1
    have h3 := integral_re (𝕜 := ℂ) hi
    simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at h3
    rw [← h3] at h2
    have h4 : 0 < ∫ g : UJ ε, a (umat g) * (⟪v, σ (umat g) v⟫_ℂ).re ∂(muG ε) := by
      refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
        (hacont.mul hre) hac.mul_right ?_ (mul_ne_zero ha1 hone.ne')
      intro g
      by_cases h : a (umat g) = 0
      · simp [h]
      · exact mul_nonneg (ha0 _) (le_of_lt (haU g h))
    rw [← h2] at h4
    simp at h4

theorem exists_isDer_kType : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H), IsURepOn (UJset ε) σ → IsKTypeOf ε σ μ S → ∃ (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (S' : Submodule ℂ H), IsDer ε σ V E ∧ IsKTypeOf ε σ μ S' ∧ S' ≤ V := by
  intro n ε μ H _ _ _ σ S hσ hK
  let G : Set H := {v | ∃ (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (s : H), SmoothOnG ε α ∧
    HasCompactSupport (fun g : UJ ε => α (umat g)) ∧
    ∀ y : H, ∫ g : UJ ε, α (umat g) * ⟪y, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪y, v⟫_ℂ}
  have hder : ∀ v ∈ Submodule.span ℂ G, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X →
      ∃ v' ∈ Submodule.span ℂ G,
        HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0 := by
    intro v hv X hX
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨α, s, h1, h2, h3⟩ := hv
      obtain ⟨β, v', k1, k2, k3, k4⟩ :=
        (GlobalTheory.GardingStep.garding_step n ε H σ α s v hσ h1 h2 h3).2 X hX
      exact ⟨v', Submodule.subset_span ⟨β, s, k1, k2, k3⟩, k4⟩
    | zero => exact ⟨0, zero_mem _, by simpa using hasDerivAt_const (0 : ℝ) (0 : H)⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha', hda⟩ := ha
      obtain ⟨b', hb', hdb⟩ := hb
      refine ⟨a' + b', add_mem ha' hb', ?_⟩
      simp only [map_add (f := _)]
      exact hda.add hdb
    | smul c a _ ha =>
      obtain ⟨a', ha', hda⟩ := ha
      refine ⟨c • a', Submodule.smul_mem _ c ha', ?_⟩
      simp only [map_smul]
      exact hda.const_smul c
  have hzero := GlobalTheory.DerEx.smoothOnG_zero ε
  have hsm : ∀ v ∈ Submodule.span ℂ G, ∀ y : H, SmoothOnG ε (fun g => ⟪y, σ g v⟫_ℂ) := by
    intro v hv y
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨α, s, h1, h2, h3⟩ := hv
      exact (GlobalTheory.GardingStep.garding_step n ε H σ α s v hσ h1 h2 h3).1 y
    | zero => simpa using hzero
    | add a b _ _ ha hb => simpa [inner_add_right] using GlobalTheory.DerEx.smoothOnG_comb 1 ha hb
    | smul c a _ ha => simpa [inner_smul_right] using GlobalTheory.DerEx.smoothOnG_comb c ha hzero
  obtain ⟨E, hE⟩ := GlobalTheory.DerOf.exists_isDer n ε H σ (Submodule.span ℂ G) hσ hder hsm
  obtain ⟨α, T, h1, h2, h3, h4, h5⟩ := exists_garding_kMap n ε μ H σ S hσ hK
  haveI := hK.1
  refine ⟨_, E, _, hE, GlobalTheory.Dec.FormF.rangeType n ε μ H σ S H σ (LinearMap.toContinuousLinearMap T) hK h4
    (fun h => h5 (LinearMap.ext fun x => DFunLike.congr_fun h x)), ?_⟩
  rintro _ ⟨s, rfl⟩
  exact Submodule.subset_span ⟨α, s, h1, h2, fun y => (h3 s y).symm⟩

end GlobalTheory.SmoothKType
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.iwasawa_integration_formula_up_to_constant : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (μN μM μK : Measure (Formalism.REAL.UJ ε)), IsGaugeSub (flagN ε W) (dimN n j) μN → IsGaugeSub (flagM ε W) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μM → μK (maxK ε)ᶜ = 0 → μK Set.univ = 1 → (∀ k ∈ maxK ε, μK.map (fun g => k * g) = μK) → ∃ κ : ENNReal, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ φ : Formalism.REAL.UJ ε → ENNReal, Measurable φ → ∫⁻ g, φ g ∂(Formalism.REAL.muG ε) = κ * ∫⁻ u, ∫⁻ m, ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) * ∫⁻ k, φ (u * m * k) ∂μK ∂μM ∂μN := by
  first | exact @GlobalTheory.IwasawaShape.iwasawa_shape | exact GlobalTheory.IwasawaShape.iwasawa_shape | (intros; apply GlobalTheory.IwasawaShape.iwasawa_shape <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.riemannianHaarGauge_volume_unitaryGroup_eq : ∀ (N : ℕ) (c : ℝ), IsGauge (allPos N) c → c * (Formalism.REAL.muG (allPos N) Set.univ).toReal = volU N := by
  first | exact @GlobalTheory.UnitaryVolume.volume_unitary | exact GlobalTheory.UnitaryVolume.volume_unitary | (intros; apply GlobalTheory.UnitaryVolume.volume_unitary <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.amplitude_one_side_unfolding : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mat k r → (Wp →L[ℂ] Wp)) (ψ : Mat k r → ℂ) (μG μW μN νS : Measure (Mt k r)) (Φ : Mat k r → Wp) (c : ℝ), OneSide z π ψ μG μW μN νS Φ c → ∀ (f : Mt k r → ℝ≥0∞) (Q : Set (Mt k r)) (Vol : ℝ≥0∞), Measurable f → MeasurableSet Q → (∀ s ∈ Sset k r z, ∀ x, Matrix.of x ∈ GG k r → (lmulM s x ∈ Q ↔ x ∈ Q)) → (∀ g ∈ GG k r, ∫⁻ n, f (rmulM g n) ∂μN ≤ Vol) → ∀ w : Wp, ‖w‖ = 1 → ∫⁻ x in Q, f x * (‖⟪w, Φ (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μG ≤ Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * ∫⁻ x in Q, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS := by
  first | exact @GlobalTheory.Amp.OnePiece.one_piece | exact GlobalTheory.Amp.OnePiece.one_piece | (intros; apply GlobalTheory.Amp.OnePiece.one_piece <;> assumption)
end

section

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_normalised_localBesselDatum : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), 1 ≤ k → IsSection k r L.z L.z' μsec → ∃ Bs : B.RealPlaceData k r L.Wp L.Wq, IsStdOf L μsec Bs := by
  first | exact @GlobalTheory.ThA.exists_isStdOf | exact GlobalTheory.ThA.exists_isStdOf | (intros; apply GlobalTheory.ThA.exists_isStdOf <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.levi_factor_integral_mod_integral_points_le : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (μM : ∀ v, Measure (Formalism.REAL.UJ (I.ε v))) [∀ v, SigmaFinite (μM v)] (c₀ : InfinitePlace I₀.F → ℝ), (∀ v, IsGaugeSub (flagM (I.ε v) (flagAt I S v)) ((I.n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) (μM v)) → IsGaugeAll I₀ c₀ → ∀ F : (Fin a → ℝ) → ENNReal, Measurable F → covol (leviGroup I xf S) ((Measure.pi μM).withDensity fun m => F (sizesAt I xf S m)) {m | ∀ v, m v ∈ flagM (I.ε v) (flagAt I S v)} ≤ (∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2)) * slabVol I.E (j i) (Λ i)) * (ENNReal.ofReal (∏ v, c₀ v) * covol (latGroup I₀ x₀) (Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) Set.univ) * ∫⁻ τ in {τ : Fin a → ℝ | ∀ i, 0 < τ i}, F τ * ENNReal.ofReal (∏ i, 2 * (I.f : ℝ) * j i / τ i) := by
  first | exact @GlobalTheory.FlagBase.LeviInt.covol_leviGroup_le | exact GlobalTheory.FlagBase.LeviInt.covol_leviGroup_le | (intros; apply GlobalTheory.FlagBase.LeviInt.covol_leviGroup_le <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.sumData_mass_be_eq_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β : ℕ, 1 ≤ β → (S.sumData fun d => S.mass d fun Λ => S.be d Λ = β) ≤ ENNReal.ofReal ((4 * S.Hp ^ (4 * (r + 1))) * ((β : ℝ) ^ (k - 1))⁻¹) * S.nn := by
  first | exact @GlobalTheory.DefectShare.mass_defect_order_le | exact GlobalTheory.DefectShare.mass_defect_order_le | (intros; apply GlobalTheory.DefectShare.mass_defect_order_le <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.amplitude_expansion_over_finite_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ d : G.Dat, (∃ Λ₀, G.IsTerm d Λ₀) → ∀ S1 : Finset (HeightOneSpectrum (𝓞 F)), G.Om ⊆ S1 → ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ Q : Prop → Prop, G.amp d (fun Λ => Q (¬ G.Gen d Λ)) = κ * ∑ B ∈ S1.powerset.filter (fun B => Q B.Nonempty), ∏ p ∈ S1, (if p ∈ B then (G.S p).amp (d p) (fun Λ => ¬ (G.S p).BBzero (d p) Λ) else (G.S p).amp (d p) ((G.S p).BBzero (d p))) := by
  first | exact @GlobalTheory.HL.DefectPhase.amp_sum_defect_sets | exact GlobalTheory.HL.DefectPhase.amp_sum_defect_sets | (intros; apply GlobalTheory.HL.DefectPhase.amp_sum_defect_sets <;> assumption)
end
