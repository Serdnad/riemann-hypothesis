module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1949
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2268
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1950
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle380
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqMulGaussianLatticeTranslateEqShifted
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianSectionIsUnitGermOfLocalIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2358
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses

@[expose] public section

section

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.StdDatum

variable {D : D7}

theorem om_sum {δ : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ} (W : WeilO D ⊤ δ a d e0) (g : GA D a) (g' : GA D d) {ι : Type}
    (s : Finset ι) (F : ι → VC D a d → ℂ) (hF : ∀ i ∈ s, F i ∈ TT D (tor0 D ⊤ δ) a d) :
    W.Om g g' (∑ i ∈ s, F i) = ∑ i ∈ s, W.Om g g' (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : (0 : VC D a d → ℂ) ∈ TT D (tor0 D ⊤ δ) a d := (GlobalTheory.FinWeil.TTs D (tor0 D ⊤ δ) a d).zero_mem
    have := W.smul g g' 0 0 h0
    simpa using this
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx,
      W.add g g' _ (hF x (Finset.mem_insert_self _ _)) _
        ((GlobalTheory.FinWeil.TTs D (tor0 D ⊤ δ) a d).sum_mem fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

theorem exists_bottom_big : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc), IsCoprime (condE G.pl) D.host.𝔟 → ∀ {δ t0 : ℂ}, Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ (i j : Fin D.R.m) (χβ : HeckeU D (botBig D i j)), (∀ x, χβ.f x = (betaH G i j)⁻¹.1 (finIdl D x)) → ∀ (χν : HeckeU D (botBig D i j + botSmall D i j)), (∀ x, χν.f x = (nuH G μ₀ i j)⁻¹.1 (finIdl D x)) → (∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χν.n τ) → ∃ P : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl), P.a = botBig D i j ∧ P.d = botBig D i j + botSmall D i j ∧ HasChars P (betaH G i j)⁻¹ (nuH G μ₀ i j)⁻¹ ∧ IsStdDatum P (condE G.pl) 0 ∧ IsBlockLevel P (condE G.pl) (botBig D i j) := by
  intro D T L sc μ₀ hL G hb δ t0 hc ht i j χβ hβ χν hν hn
  have hd : Even (botBig D i j + botSmall D i j) := by
    obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
    exact ⟨halfRank D i j - (D.R.m - (j + 1)) / 2 - (D.R.m - j) / 2, by omega⟩
  have had : botBig D i j ≤ botBig D i j + botSmall D i j := Nat.le_add_right _ _
  obtain ⟨e0, vac, h0⟩ := GlobalTheory.Vacuum.exists_vacuum D ⊤ δ hc t0 ht _ _ (hd.mul_left (botBig D i j))
  obtain ⟨W, hW1, hW2, hW3, hW4⟩ := GlobalTheory.FinWeil.exists_weil_of_vacuum D ⊤ δ hc _ _ e0 vac.1 h0 χβ χν
  have hm : condE G.pl ≠ ⊥ := condE_ne_bot _
  have hcop := GlobalTheory.FunObj.StdDatum.condE_isCoprime_conj G.pl
  have hnu : ∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (condE G.pl * D.host.conj • condE G.pl) → W.chV'.f u = 1 := by
    rw [hW2]; exact GlobalTheory.FunObj.SqNum.heckeU_nuInv_eq_one_of_cong hL G i j χν hν
  obtain ⟨hi0, -⟩ := GlobalTheory.congLev_relIndex_le D (condE G.pl) hm (botBig D i j)
  obtain ⟨R, hR1, hR2'⟩ := GlobalTheory.exists_finset_leftTransversal_of_relIndex_ne_zero (intG D (botBig D i j)) (congLev D (condE G.pl) (botBig D i j)) (congLev_le _ _) hi0
  have hR2 : ∀ k ∈ intG D (botBig D i j), ∃! r, r ∈ R ∧ CongOne D (condE G.pl) (r⁻¹ * k) := by
    intro k hk
    obtain ⟨r, ⟨hr, hrk⟩, hu⟩ := hR2' k hk
    refine ⟨r, ⟨hr, ((GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).1 hrk).2⟩, fun r' ⟨hr', h'⟩ => hu r' ⟨hr', (GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).2
      ⟨mul_mem (inv_mem (hR1 r' hr')) hk, h'⟩⟩⟩
  have hcv := GlobalTheory.FunObj.CosetTT.cosetV_mem_TT D δ hc (condE G.pl) hm 0 _ _ e0 vac.1
  have hfix : ∀ k ∈ intG D (botBig D i j), W.Om k 1 (stdSum W (condE G.pl) 0 R) = stdSum W (condE G.pl) 0 R := by
    intro k hk
    unfold stdSum
    rw [om_sum W k 1 R _ fun r _ => W.maps _ _ _ hcv]
    have e1 : ∀ r, W.Om k 1 (W.Om r 1 (cosetV D δ (condE G.pl) 0 _ _ e0)) = W.Om (k * r) 1 (cosetV D δ (condE G.pl) 0 _ _ e0) := by
      intro r
      have := W.mul k r 1 1 _ hcv
      rw [mul_one] at this
      exact this.symm
    simp_rw [e1]
    refine GlobalTheory.sum_transversal_left_translate_invariant (intG D (botBig D i j)) (congLev D (condE G.pl) (botBig D i j)) R
      (fun g => W.Om g 1 (cosetV D δ (condE G.pl) 0 _ _ e0)) hR1 hR2' (fun r _ c hc' => ?_) k hk
    have := W.mul r c 1 1 _ hcv
    rw [mul_one] at this
    obtain ⟨hc1, hc2⟩ := (GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).1 hc'
    rw [this, GlobalTheory.T.weil_fixes_cosetVector_congruent_one_mod_ideal D δ t0 hc e0 vac W (condE G.pl) hm hcop hnu 0 (by omega) c hc1 hc2]
  have hle : congLev D (condE G.pl) (botBig D i j + botSmall D i j) ≤
      blockLev D (condE G.pl) (botBig D i j + botSmall D i j) (botBig D i j) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := (GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).1 hk
    refine (GlobalTheory.FunObj.StdDatum.BlockMem.mem_iff _ _ _ _ _).2 ⟨hk1, fun a b hb ha => ?_⟩
    have hab : a ≠ b := fun e => by rw [e] at ha; omega
    have := hk2 a b
    rwa [Matrix.sub_apply, Matrix.one_apply_ne hab, sub_zero] at this
  obtain ⟨hj0, hj1⟩ := GlobalTheory.congLev_relIndex_le D (condE G.pl) hm (botBig D i j + botSmall D i j)
  have hQ : 0 < levQ G.pl := by
    rw [← GlobalTheory.FunObj.NormLevel.absNorm_condE]; exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hm)
  let n : D.what₂.Tau → ℕ := fun τ => ((χν.n τ - (botBig D i j + botSmall D i j : ℕ)) / 2).toNat
  have hwt : ∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ) := by
    intro τ
    rw [hW4, hW2, one_mul]
    obtain ⟨r, hr⟩ := χν.par τ
    have h1 := hn τ
    have h2 : ((χν.n τ - (botBig D i j + botSmall D i j : ℕ)) / 2) = r := by omega
    simp only [n, h2]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have hpres : Pres D ⊤ δ (levQ G.pl) e0 (stdSum W (condE G.pl) 0 R) := by
    rw [← GlobalTheory.FunObj.NormLevel.absNorm_condE]
    exact GlobalTheory.T.standardTheta_datum_presentation_level_norm D δ t0 hc e0 vac had W _ hm hcop hb hnu R hR1 hR2 hfix
  have hidx_ne : (blockLev D (condE G.pl) (botBig D i j + botSmall D i j) (botBig D i j)).relIndex
      (intG D (botBig D i j + botSmall D i j)) ≠ 0 := fun h =>
    hj0 (Subgroup.relIndex_eq_zero_of_le_left hle h)
  have hidx_le : (blockLev D (condE G.pl) (botBig D i j + botSmall D i j) (botBig D i j)).relIndex
      (intG D (botBig D i j + botSmall D i j)) ≤ levQ G.pl ^ ((botBig D i j + botSmall D i j) ^ 2 + 4) := by
    refine (Subgroup.relIndex_le_of_le_left hle hj0).trans (hj1.trans ?_)
    rw [GlobalTheory.FunObj.NormLevel.absNorm_condE]
    exact Nat.pow_le_pow_right hQ (by omega)
  have heig := GlobalTheory.T.standardThetaDatum_eigenvector_blockLevel D δ t0 hc e0 vac had W _ hm hcop hnu R hR1 hR2 hfix
  let P : Pair D ⊤ δ t0 (levQ G.pl) :=
    { crv := hc
      pt0 := ht
      a := botBig D i j
      d := botBig D i j + botSmall D i j
      a_le := had
      d_even := hd
      e0 := e0
      vac := vac
      W := W
      n := n
      wt := hwt
      F := stdSum W (condE G.pl) 0 R
      pres := hpres
      fix := hfix
      J := blockLev D (condE G.pl) (botBig D i j + botSmall D i j) (botBig D i j)
      J_le := blockLev_le _ _ _
      idx_ne := hidx_ne
      idx_le := hidx_le
      eig := heig }
  refine ⟨P, rfl, rfl, ⟨fun x => ?_, fun x => ?_⟩, ⟨R, hR1, hR2, rfl⟩, fun h => GlobalTheory.FunObj.StdDatum.BlockMem.mem_iff _ _ _ _ h⟩
  · show W.chV.f x ^ W.ep = _
    rw [hW1, hW3, zpow_one, hβ]
  · show W.chV'.f x ^ W.ep' = _
    rw [hW2, hW4, zpow_one, hν]

end GlobalTheory.FunObj.StdDatum

end
end

section

set_option autoImplicit false

noncomputable section

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.CotIndep

open IsLocalRing TensorProduct

theorem tmul_D_eq_zero_of_mem_sq (k P : Type*) [CommRing k] [CommRing P] [IsLocalRing P]
    [Algebra k P] {x : P} (hx : x ∈ maximalIdeal P ^ 2) :
    (1 : ResidueField P) ⊗ₜ[P] KaehlerDifferential.D k P x = 0 := by
  have hker : RingHom.ker (algebraMap P (ResidueField P)) = maximalIdeal P := ker_residue
  have hx' : x ∈ RingHom.ker (algebraMap P (ResidueField P)) := by
    rw [hker]; exact Ideal.pow_le_self two_ne_zero hx
  have h0 : (RingHom.ker (algebraMap P (ResidueField P))).toCotangent ⟨x, hx'⟩ = 0 := by
    rw [Ideal.toCotangent_eq_zero]
    change x ∈ _ ^ 2
    rw [hker]; exact hx
  have := congrArg (KaehlerDifferential.kerCotangentToTensor k P (ResidueField P)) h0
  rwa [KaehlerDifferential.kerCotangentToTensor_toCotangent, map_zero] at this

theorem linearIndependent_toCotangent {k A P : Type*} [CommRing k] [CommRing A] [CommRing P]
    [IsLocalRing P] (α : k →+* A) (ρ : A →+* P)
    (hρ : letI := ρ.toAlgebra; Algebra.FormallyEtale A P) {n : ℕ} (z : Fin n → A)
    (hω : IsFreeGen A (dForm α z)) (J : Finset (Fin n))
    (hz : ∀ j : J, ρ (z j) ∈ maximalIdeal P) :
    LinearIndependent (ResidueField P)
      (fun j : J => ((maximalIdeal P).toCotangent ⟨ρ (z j), hz j⟩ : CotangentSpace P)) := by
  classical
  have h1 : IsFreeGen P (dForm (ρ.comp α) fun i => ρ (z i)) := by
    have := MorJac.isFreeGen_formMap (D := n) hρ rfl hω
    rwa [formMap_dForm] at this
  letI := (ρ.comp α).toAlgebra
  set κ := ResidueField P
  let φ : Omega (ρ.comp α) →ₗ[P] κ ⊗[P] Omega (ρ.comp α) := TensorProduct.mk P κ _ 1
  have h2 := h1.of_isBaseChange
    (isBaseChange_exteriorPower (TensorProduct.isBaseChange P (Omega (ρ.comp α)) κ) n)
  rw [dForm_eq, exteriorPowerMapOver_ιMulti] at h2
  have h3 : exteriorPower.ιMulti κ n (fun i => φ (dFun (ρ.comp α) (ρ (z i)))) ≠ 0 := by
    intro h0
    rw [h0] at h2
    exact one_ne_zero (h2.1 (a₁ := (1 : κ)) (a₂ := 0) (by simp))
  have h4 : LinearIndependent κ (fun i => φ (dFun (ρ.comp α) (ρ (z i)))) := by
    by_contra h
    exact h3 (AlternatingMap.map_linearDependent _ _ h)
  have h5 := h4.comp (Subtype.val : J → Fin n) Subtype.val_injective
  rw [Fintype.linearIndependent_iff] at h5 ⊢
  intro g hg i
  choose b hb using fun j => residue_surjective (R := P) (g j)
  have hsq : ∑ j : J, b j * ρ (z j) ∈ maximalIdeal P ^ 2 := by
    have e : ∑ j : J, g j • ((maximalIdeal P).toCotangent ⟨ρ (z j), hz j⟩ : CotangentSpace P) =
        (maximalIdeal P).toCotangent (∑ j : J, b j • (⟨ρ (z j), hz j⟩ : maximalIdeal P)) := by

      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← hb j, ← ResidueField.algebraMap_eq, algebraMap_smul]
    rw [e, Ideal.toCotangent_eq_zero] at hg
    simpa [Submodule.coe_sum] using hg
  have h0 := tmul_D_eq_zero_of_mem_sq k P hsq
  have htk : ∀ j : J, algebraMap P κ (ρ (z j)) = 0 := fun j => by
    rw [ResidueField.algebraMap_eq]; exact (residue_eq_zero_iff _).2 (hz j)
  refine h5 g ?_ i

  rw [← h0, map_sum, tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.leibniz, tmul_add, ← smul_tmul, ← smul_tmul, Algebra.smul_def, mul_one,
    Algebra.smul_def, mul_one, htk, zero_tmul, add_zero, ← hb j, ← ResidueField.algebraMap_eq]
  change (algebraMap P κ (b j)) • ((1 : κ) ⊗ₜ[P] KaehlerDifferential.D k P (ρ (z j))) = _
  rw [smul_tmul', smul_eq_mul, mul_one]

end GlobalTheory.CotIndep

namespace GlobalTheory.CotIndep

theorem linearIndependent_cotangent_of_isFrame : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (U : Y.Opens) (z : Fin n → Γ(Y, U)), IsFrame (dOn q z) → ∀ (y : Y) (hy : y ∈ U) (J : Finset (Fin n)) (hz : ∀ j : J, Y.presheaf.germ U y hy (z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨(fun j : J => Y.presheaf.germ U y hy (z j)) j, hz j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y))) := by
  intro Y _ _ q n _ U z hf y hy J hz
  exact linearIndependent_toCotangent (algX q U) (Y.presheaf.germ U y hy).hom
    (MorJac.formallyEtale_germ hf.affine y hy) z hf.gen J hz

end GlobalTheory.CotIndep
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.exists_bijective_stalkMap_over_dvrPoint : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (U : Y.Opens) (d : ℕ)
    (M : Modif p U d), IsProjOver p → (U : Set Y).Nonempty → ∀ y : Y, IsDiscreteValuationRing (Y.presheaf.stalk y) →
      ∃ x : M.X, M.σ x = y ∧ Function.Bijective (M.σ.stalkMap x).hom := by
  first | exact @GlobalTheory.CompHS.Modif.exists_bijective_stalkMap_of_dvr | exact GlobalTheory.CompHS.Modif.exists_bijective_stalkMap_of_dvr | (intros; apply GlobalTheory.CompHS.Modif.exists_bijective_stalkMap_of_dvr <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.germ_mem_range_stalk_of_pullback_mul_localIso : ∀ (k : Type) [CommRing k] (Y X : Scheme.{0}) [IsIntegral Y] [IsIntegral X]
    (p : Y ⟶ Sp k) (σ : X ⟶ Y) (U : Y.Opens) [IsIso (σ ∣_ U)] [Nonempty U] (L : LB Y) (P N : LB X)
    (C : ProdChart P (L.pull σ) N) (J : H0 (σ ≫ p) P ⊤) (g : H0 (σ ≫ p) N ⊤) (s : H0 p L U),
    C.mul (H0.restr le_top J) (H0.pull σ le_rfl s) = H0.restr le_top g → ∀ x : X,
      Function.Bijective (σ.stalkMap x).hom → (∀ (a : P.ι) (ha : x ∈ P.U a), IsUnit (H0.germ a x (memTop x) ha J)) →
      ∀ (i : L.ι) (hi : σ x ∈ L.U i) [Nonempty (U ⊓ L.U i : Y.Opens)],
        Y.germToFunctionField (U ⊓ L.U i) (s.loc i) ∈ (algebraMap (Y.presheaf.stalk (σ x)) Y.functionField).range := by
  first | exact @GlobalTheory.germToFunctionField_mem_range_stalk_of_mul_pull | exact GlobalTheory.germToFunctionField_mem_range_stalk_of_mul_pull | (intros; apply GlobalTheory.germToFunctionField_mem_range_stalk_of_mul_pull <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.isIntegral_smoothProjectiveModification_of_nonempty : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (U : Y.Opens) (d : ℕ)
    (M : Modif p U d), (U : Set Y).Nonempty → IsIntegral M.X := by
  first | exact @GlobalTheory.isIntegral_of_nonempty_modif | exact GlobalTheory.isIntegral_of_nonempty_modif | (intros; apply GlobalTheory.isIntegral_of_nonempty_modif <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.exists_jacobian_section_isUnit_germ_of_localIso : ∀ (F : Type) [Field F] (Y X : Scheme.{0}) (p : Y ⟶ Sp F) (σ : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d p] [SmoothOfRelativeDimension d (σ ≫ p)] (K : CanonLB p d) (K' : CanonLB (σ ≫ p) d),
    ∃ J : H0 (σ ≫ p) (LB.div K'.bundle (K.bundle.pull σ)) ⊤, ∀ x : X, Function.Bijective (σ.stalkMap x).hom →
      ∀ (a : (LB.div K'.bundle (K.bundle.pull σ)).ι) (ha : x ∈ (LB.div K'.bundle (K.bundle.pull σ)).U a),
        IsUnit (H0.germ a x (memTop x) ha J) := by
  first | exact @GlobalTheory.exists_jacobian_section_isUnit_germ | exact GlobalTheory.exists_jacobian_section_isUnit_germ | (intros; apply GlobalTheory.exists_jacobian_section_isUnit_germ <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NumPull

theorem isNef_pull_of_isProjOver : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (s : Y ⟶ X), IsProjOver p → ∀ N : LB X, (letI := algebraΓOfHom p; IsNef k N) → (letI := algebraΓOfHom (s ≫ p); IsNef k (N.pull s)) := by
  intro k _ X Y p s hp N hN
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (s ≫ p)
  have : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  refine ⟨pull_isLB hN.isLB s, fun C hC => ?_⟩
  rcases interNumRed_pull_curve p s C hC with h | ⟨C', hC', d, hd⟩
  · rw [h N hN.isLB]
  · rw [hd N hN.isLB]
    exact mul_nonneg (Int.natCast_nonneg d) (hN.nonneg C' hC')

end GlobalTheory.NumPull
end
end

section

open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

namespace GlobalTheory.BigTop.Fun.Close

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cloudIcc {D : D7} (L : SizeData₂ D) (τ i : ℕ) :
    0 ≤ cloud D τ i ∧ (cloud D τ i : ℝ) ≤ L.Sc := by
  unfold cloud
  split_ifs with h
  · dsimp only [GlobalTheory.SignedHC.GridData.ofHCParam]
    unfold GlobalTheory.SignedHC.GridData.extend
    split_ifs with h2
    · obtain ⟨h0, h1⟩ := L.cloud_v ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩) ⟨i - 2, h2⟩
      refine ⟨Int.floor_nonneg.mpr (by exact_mod_cast h0), ?_⟩
      have hf := Int.floor_le ((D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)).v ⟨i - 2, h2⟩)
      have hf' : (((⌊(D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)).v ⟨i - 2, h2⟩⌋ : ℤ) : ℚ) : ℝ) ≤
          (((D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)).v ⟨i - 2, h2⟩ : ℚ) : ℝ) := by exact_mod_cast hf
      push_cast at hf' ⊢
      linarith
    · exact ⟨le_rfl, by simpa using L.Sc_pos.le⟩
  · exact ⟨le_rfl, by simpa using L.Sc_pos.le⟩

theorem lcLeOfCloud {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}
    (O : FunData K Df) (S : ℝ) (h0 : 0 ≤ S) (hcl : ∀ τ i, 0 ≤ O.cl τ i ∧ (O.cl τ i : ℝ) ≤ S) :
    (O.Lc : ℝ) ≤ S := by
  have hL : O.Lc ≤ ⌊S⌋₊ := by
    unfold FunData.Lc
    refine Finset.sup_le fun τ _ => ?_
    rw [Nat.le_floor_iff h0]
    obtain ⟨a0, a1⟩ := hcl τ 2
    obtain ⟨b0, -⟩ := hcl τ O.k
    have h : ((O.cl τ 2 - O.cl τ O.k).toNat : ℤ) ≤ O.cl τ 2 := by omega
    have h' : (((O.cl τ 2 - O.cl τ O.k).toNat : ℤ) : ℝ) ≤ ((O.cl τ 2 : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  calc (O.Lc : ℝ) ≤ (⌊S⌋₊ : ℝ) := by exact_mod_cast hL
    _ ≤ S := Nat.floor_le h0

theorem scLeB {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) : L.Sc ≤ L.sc.b := by
  have hk := P.kS_le
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hn : (1 : ℝ) ≤ D.R.n := by
    unfold Ranks.n
    exact_mod_cast (show 1 ≤ D.R.ord from D.R.ord_pos)
  have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hX : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg hx.le _)
  have hw : L.sc.w'' D.R.n ≤ L.sc.b := by
    unfold Scale.w'' Scale.b' Scale.a
    rw [div_le_iff₀ (by positivity)]
    calc L.sc.x * L.sc.b / L.sc.X' ≤ L.sc.x * L.sc.b := div_le_self (by positivity) hX
      _ ≤ L.sc.b * (L.sc.x * D.R.n) := by nlinarith [mul_nonneg (mul_pos hx hb).le (sub_nonneg.2 hn)]
  have hS := L.Sc_pos
  nlinarith

end GlobalTheory.BigTop.Fun.Close
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

theorem _root_.GlobalTheory.T.realPoints_act_fock_vectors_any_datum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (φ : WO (Vc D i) (Wc D i) → ℂ), IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) R.Pg Q ξR (R.vacP i) φ → ∀ u ∈ GinfC (Vc D i), ∀ x w, R.ωP i A.μ0 (u, 1) (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ (R.ioP i x w)) = pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ (R.ioP i x ((R.cV i).ρ u w)) := by
  first | exact @GlobalTheory.FockAnyDatum.om_ioP_of_datum | exact GlobalTheory.FockAnyDatum.om_ioP_of_datum | (intros; apply GlobalTheory.FockAnyDatum.om_ioP_of_datum <;> assumption)
end
