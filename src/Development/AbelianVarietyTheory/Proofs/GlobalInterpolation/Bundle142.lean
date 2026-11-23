module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle110
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle120
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle133
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle037
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle040
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalToGlobal.Columns.TiedValBwG
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle046
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NegGram
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle107
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle087
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle106
import Formalism.LocalToGlobal.Divisibility.ClassSumLemmas
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle140
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle093
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle017
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
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct


theorem _root_.GlobalTheory.T.adicIntegersCharacterDualIndex_eq_residue_card_zpow : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (c : ℤ), (∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp c) → LocalAdditiveCharacterDual.nIdx F ψ v = (PlaceSplittingTypes.resCard F v : ℝ) ^ c := by
  first | exact @GlobalTheory.DualIndexPow.nIdx_eq_zpow | exact GlobalTheory.DualIndexPow.nIdx_eq_zpow | (intros; apply GlobalTheory.DualIndexPow.nIdx_eq_zpow <;> assumption)
end

section

namespace GlobalTheory.Proof.cm_localDensities_productFormula

theorem densityProduct : GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.DensityProduct :=
  fun F E _ _ _ _ _ _ σ h₁ h₂ h₃ =>
    ⟨GlobalTheory.T.existsUnique_isStandardAdeleChar_unramifiedCM_base F E σ h₁ h₂ h₃, GlobalTheory.T.dual_lattice_different_index F E σ h₁ h₂ h₃, GlobalTheory.T.finprod_localDifferentIdealNorm_eq_discr F E σ h₁ h₂ h₃,
      GlobalTheory.T.exists_eq_standardAdeleChar_rational_dilate F E σ h₁ h₂ h₃, GlobalTheory.T.hasProd_quadExtLocalEulerFactorInv_inv F E σ h₁ h₂ h₃, GlobalTheory.T.product_localDensities_adeleCharacter F E σ h₁ h₂ h₃⟩

end GlobalTheory.Proof.cm_localDensities_productFormula
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2

theorem mem_locW_hlat_iff : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K)), (∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) → ∀ {n : ℕ} (S : GStep E K n) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok), S.Ok → ∀ (w : Pl.Pl) (x : (S.hlat emb lam h).V), x ∈ locW Pl w (S.hlat emb lam h).L ↔ ∀ c, x.1 c ∈ locW Pl w (delAtr emb lam (S.Lsh c.1 (S.rep c))) := by
  intro E K ι _ _ _ _ _ _ _ emb Pl pw hv n S lam h hS w x
  unfold locW
  simp only [vl_mem_span_intW_iff Pl pw hv]
  unfold Formalism.HermitianLatticesTheory.localization₂
  constructor
  · rintro ⟨s, hs, hsx⟩ c
    exact ⟨s, hs, hsx c⟩
  · classical
    intro hx
    choose t ht htx using hx
    have : ∀ b, Finite (MulAction.orbitRel.Quotient (S.G b) (S.D b)) := hS.fin_orb
    let _ : Fintype S.Cl := Fintype.ofFinite _
    refine ⟨∏ c, t c, Submonoid.prod_mem _ fun c _ => ht c, fun c => ?_⟩
    have hc := (delAtr emb lam (S.Lsh c.1 (S.rep c))).smul_mem (∏ d ∈ Finset.univ.erase c, t d) (htx c)
    rw [← mul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ c)] at hc
    exact hc

end GlobalTheory.Mem.Col2
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ

theorem ctx_exists : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (N : ℕ) (a : Fin N → F), (∀ l, a l ≠ 0) → ∃ lam ν, Ctx ψ lam ν a := by
  intro F _ _ hF ψ hψ N a ha
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.exists_archimedean_exponents_adeleCharacter F hF ψ hψ
  obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_measure_isCov1 F
  refine ⟨lam, ν, ?_⟩
  unfold Ctx
  exact ⟨hF, hψ, hlam, hν, ha⟩

end GlobalTheory.SWQ
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.volume_negativeDefinite_eq_opposite : ∀ D : D7, VolTie D → ∀ (W : HSpace D.host.E) (n : ℕ), W.SigOK → (∀ τ, W.sig τ = (0, n)) → D.vol W = D.vol (GlobalTheory.NegSpace.neg W) := by
  first | exact @GlobalTheory.NegVol.vol_neg_eq | exact GlobalTheory.NegVol.vol_neg_eq | (intros; apply GlobalTheory.NegVol.vol_neg_eq <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.ThetaMove.SeamMoves

variable {X : Fields} {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
  (cD : D.what₂.Tau → ℂ)

def reidx (a b : ℕ) : VCx X.Tau a b ≃ₗ[ℂ] TaylorLogMetric.VC D a b := LinearEquiv.funCongrLeft ℂ (Fin b → Fin a → ℂ) s.iT.symm

theorem form_reidx (A : ℝ) (a b : ℕ) (x y : VCx X.Tau a b) :
    formV A D.what₂.Tau a b (reidx s a b x) (reidx s a b y) = Formalism.L2.Ker.HV A⁻¹ x y := by
  change (∑ τ, ∑ i, ∑ j, x (s.iT.symm τ) i j * (starRingEnd ℂ) (y (s.iT.symm τ) i j)) / (A : ℂ) =
    ((A⁻¹ : ℝ) : ℂ) * ∑ τ, ∑ i, ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j)
  rw [Equiv.sum_comp s.iT.symm (fun τ => ∑ i, ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j)), Complex.ofReal_inv, div_eq_inv_mul]

theorem isHerm_formV (A : ℝ) (n : Type) [Fintype n] (a b : ℕ) : IsHerm (formV A n a b) := by
  intro x y

  simp [formV, map_sum, mul_comm]

theorem iop_eq {a b : ℕ} (Λ₁ Λ₂ : AddSubgroup (TaylorLogMetric.VC D a b)) (G : TaylorLogMetric.VC D a b → ℂ) :
    TaylorLogMetric.Iop D B.tor Λ₁ Λ₂ G = inter (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) Λ₁ Λ₂ G := rfl

theorem alV_eq {a b : ℕ} (x : VCx X.Tau a b) {m : ℤ}
    (hm : Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D B.tor (reidx s a b x) (reidx s a b x)).re = (m : ℝ)) :
    alV D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ x = TaylorLogMetric.al D B.tor (reidx s a b x) := by
  have h1 : TaylorLogMetric.Hf D B.tor (reidx s a b x) (reidx s a b x) = Formalism.L2.Ker.HV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ x x :=
    form_reidx s _ a b x x
  unfold TaylorLogMetric.al
  rw [hm, round_intCast]
  rw [h1] at hm
  unfold alV alphaQ Formalism.L2.Th1.H.qOf
  rw [hm, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

include B in
theorem delta_ne_zero : δ ≠ 0 := by
  rintro rfl
  have h1 : B.L.ω₁ ∈ B.L.lattice.toAddSubgroup := B.L.ω₁_mem_lattice
  have h2 : TaylorLogMetric.lamOf D cc 0 ≤ ⊥ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨c, -, rfl⟩
    simp
  rw [B.lat] at h1
  have h3 : B.L.ω₁ = 0 := AddSubgroup.mem_bot.1 (h2 h1)
  exact B.L.indep.ne_zero 0 h3

theorem aa_ne_bot (hcc : cc ≠ ⊥) : (ambOf s B χ cD).AA ≠ ⊥ := by
  intro h
  have h1 : ((Ideal.absNorm cc : ℕ) : X.E) ∈ (ambOf s B χ cD).AA := by
    refine Submodule.subset_span ⟨_, Ideal.absNorm_mem cc, 1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, ?_⟩
    simp
  rw [h, Submodule.mem_bot, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at h1
  exact hcc h1

theorem aa_fg : (ambOf s B χ cD).AA.FG := by
  let j : 𝓞 D.host.E →+* 𝓞 X.E := RingOfIntegers.mapRingHom (s.iE.symm : D.host.E →+* X.E)
  have hj : ∀ a : 𝓞 D.host.E, ((j a : 𝓞 X.E) : X.E) = s.iE.symm (a : D.host.E) := fun _ => rfl
  obtain ⟨z, hz, hden⟩ := D.host.AA0.isFractional
  have hz0 : j z ≠ 0 := fun h => nonZeroDivisors.ne_zero hz (by
    have h1 := hj z
    rw [h] at h1
    have h2 : (z : D.host.E) = 0 := s.iE.symm.injective (by rw [← h1]; simp)
    exact RingOfIntegers.coe_injective (by simpa using h2))
  have hfr : IsFractional (nonZeroDivisors (𝓞 X.E)) (ambOf s B χ cD).AA := by
    refine (FractionalIdeal.isFractional_span_iff).2 ⟨j z, mem_nonZeroDivisors_of_ne_zero hz0, ?_⟩
    rintro r ⟨c, -, t, ht, rfl⟩
    obtain ⟨w, hw⟩ := hden t ht
    refine ⟨j (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w), ?_⟩
    rw [Algebra.smul_def]
    change ((j _ : 𝓞 X.E) : X.E) = ((j z : 𝓞 X.E) : X.E) * _
    rw [hj, hj, ← map_mul]
    congr 1
    have e : ((algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w : 𝓞 D.host.E) : D.host.E) =
      ((c : D.host.K) : D.host.E) * (w : D.host.E) := rfl
    have hw' : (w : D.host.E) = (z : D.host.E) * t := by rw [Algebra.smul_def] at hw; exact hw
    rw [e, hw']
    ring
  exact FractionalIdeal.fg_of_isNoetherianRing le_rfl ⟨_, hfr⟩

theorem vac_eq {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (h : Base.chiFac χ a b (s.lat N) (s.lat N') ≠ 0) :
    vac (ambOf s B χ cD) N N' = fun z => B.thMoved a b (s.lat N) (s.lat N') (reidx s a b z) := by
  funext z
  exact inv_mul_cancel_left₀ h _

theorem moves_ambOf : ∀ (X : Fields) (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), X.Ok → s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsChi D χ → B.EqP χ → B.LatAll → B.ThZeroMem a b → Even a → Even b → Moves (ambOf s B χ cD) a b := by
  intro X D s cc δ B χ cD a b hX hs hcc hχ hE hL hZ ha hb
  obtain ⟨hsd, hlam⟩ := GlobalTheory.T.fieldIso_selfDual_and_periodLattices_agree X D s cc δ B χ cD hs
  obtain ⟨hth, hm1, hm2⟩ := GlobalTheory.T.movedVacuum_mem_thetaFunctions_and_moves D cc δ B χ a b hχ hE hL hZ ha hb
  have hq := GlobalTheory.T.quadraticForm_integral_of_selfDual_periodLattices D cc δ B hL
  have hadm : ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
      TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := fun N N' h h' => ⟨ha, hb, hsd _ _ h, hsd _ _ h'⟩
  have key := fun (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E a)) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b)) (h : IsSdLat N₂)
      (h' : IsSdLat N₂') (θ : TaylorLogMetric.VC D a b → ℂ) =>
    Transport.inter_transport _ _ (reidx s a b) (Formalism.L2.Ker.HV (ambOf s B χ cD).sc)
      (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (alV (ambOf s B χ cD).d (ambOf s B χ cD).sc) (TaylorLogMetric.al D B.tor)
      (lam (ambOf s B χ cD) N₁ N₁') (lam (ambOf s B χ cD) N₂ N₂') (TaylorLogMetric.La D B.tor (s.lat N₁) (s.lat N₁'))
      (TaylorLogMetric.La D B.tor (s.lat N₂) (s.lat N₂')) θ (form_reidx s _ a b) (hlam a b N₁ N₁') (hlam a b N₂ N₂')
      (fun x hx => by
        obtain ⟨m, hm⟩ := hq a b _ _ (hadm N₂ N₂' h h') (reidx s a b x) ((hlam a b N₂ N₂' x).1 hx)
        exact alV_eq s B x hm)
      (isHerm_formV _ _ _ _) (hL.1 a b _ _ (hadm N₂ N₂' h h')).1 (hL.1 a b _ _ (hadm N₂ N₂' h h')).2
  refine ⟨delta_ne_zero B, Fintype.card_pos_iff.1 hX.f_pos, aa_fg s B χ cD, aa_ne_bot s B χ cD hcc.1, ?_, ?_, ?_⟩
  · intro N N' h h'
    obtain ⟨hc, han, hfix⟩ := hth _ _ (hsd _ _ h) (hsd _ _ h')
    obtain ⟨h1, h2, h3⟩ := (key N N N' N' h h' 0).1
    refine ⟨hc, ?_, h1, h2⟩
    rw [vac_eq s B χ cD N N' hc]
    refine ⟨fun z _ => ?_, h3 _ hfix⟩
    exact (han _ (Set.mem_univ _)).comp ((reidx s a b).toLinearMap.toContinuousLinearMap.analyticAt z)
  · intro N N' N'' h h' h''
    obtain ⟨hc, -, hfix⟩ := hth _ _ (hsd _ _ h) (hsd _ _ h')
    rw [vac_eq s B χ cD N N' hc, vac_eq s B χ cD N N'' (hth _ _ (hsd _ _ h) (hsd _ _ h'')).1,
      (key N N N' N'' h h'' _).2 hfix (hL.2 a b _ _ _ _ (hadm N N' h h') (hadm N N'' h h'')).1,
      hm1 _ _ _ (hsd _ _ h) (hsd _ _ h') (hsd _ _ h''), iop_eq]
  · intro N N₁ N' h h₁ h'
    obtain ⟨hc, -, hfix⟩ := hth _ _ (hsd _ _ h) (hsd _ _ h')
    rw [vac_eq s B χ cD N N' hc, vac_eq s B χ cD N₁ N' (hth _ _ (hsd _ _ h₁) (hsd _ _ h')).1,
      (key N N₁ N' N' h₁ h' _).2 hfix (hL.2 a b _ _ _ _ (hadm N N' h h') (hadm N₁ N' h₁ h')).1,
      hm2 _ _ _ (hsd _ _ h) (hsd _ _ h₁) (hsd _ _ h'), iop_eq]

end GlobalTheory.ThetaMove.SeamMoves
end
end

section

noncomputable section

namespace GlobalTheory.PeriodOnStep

open NumberField IsDedekindDomain Module Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.PeriodClassSum
open scoped Matrix ComplexOrder

theorem wForm_sum {C ι κ : Type} [Fintype C] [Fintype ι] [Fintype κ] (w : C → ℕ) (G : Matrix ι ι ℂ) (u : κ → C → ι → ℂ)
    (a b : κ → ℂ) : star a ⬝ᵥ (Matrix.of fun i j => wForm w G (u i) (u j)) *ᵥ b = wForm w G (∑ i, a i • u i) (∑ i, b i • u i) := by
  rw [dotProduct]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
  simp only [wForm, Finset.sum_apply, Pi.smul_apply, star_sum, star_smul, sum_dotProduct, smul_dotProduct,
    Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
    Pi.star_apply]
  conv_rhs => rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => by ring

section Metric

variable {K : Type} [Field K] [NumberField K] [StarRing K]


omit [NumberField K] in
theorem map_pair {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] (b : Basis ι K V) (p : V →ₗ⋆[K] V →ₗ[K] K)
    (φ : K →+* ℂ) (x y : V) (hx : ∀ i, b.repr x i ∈ cmMax K) :
    φ (p x y) = star (fun i => φ (b.repr x i)) ⬝ᵥ (Matrix.of fun i j => p (b i) (b j)).map φ *ᵥ fun i => φ (b.repr y i) := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]

  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_mul, dotProduct,
  Matrix.mulVec, Matrix.map_apply, Matrix.of_apply, Finset.mul_sum, RingHom.id_apply, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply, hx i φ, starRingEnd_apply]
  ring

variable (S : CSD K) (v : InfinitePlace K)

def coAt (f : S.Cl → S.V) : S.Cl → S.ιV → ℂ := fun c i => v.embedding (S.bV.repr (f c) i)

theorem coAt_sum (x : S.Forms) :
    coAt S v (x : S.Cl → S.V) = ∑ i, v.embedding (S.basis.repr x i) • coAt S v (S.basis i : S.Cl → S.V) := by
  funext c k
  conv_lhs => rw [← S.basis.sum_repr x]

  simp only [coAt, AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, map_sum,
  map_smul, smul_eq_mul]
  simp

theorem coAt_indep : LinearIndependent ℂ fun i => fun p : S.Cl × S.ιV => coAt S v (S.basis i : S.Cl → S.V) p.1 p.2 := by
  letI : Algebra K ℂ := v.embedding.toAlgebra
  let f : S.Forms →ₗ[K] (S.Cl × S.ιV → K) := LinearMap.pi fun p =>
    S.bV.coord p.2 ∘ₗ LinearMap.proj p.1 ∘ₗ S.Forms.subtype
  have hf : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro φ hφ
    apply Subtype.ext
    funext c
    exact S.bV.forall_coord_eq_zero_iff.1 fun k => congrFun hφ (c, k)
  exact (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 (S.basis.linearIndependent.map' f hf)

theorem H_map (hb : S.HasRatBasis) : S.H.map v.embedding = Matrix.of fun i j =>
    wForm S.wt (S.gramV.map v.embedding) (coAt S v (S.basis i : S.Cl → S.V)) (coAt S v (S.basis j : S.Cl → S.V)) := by
  ext i j

  simp only [Matrix.map_apply, CSD.H, Matrix.of_apply, CSD.csum, wForm, map_sum, map_mul, map_inv₀, map_natCast]
  exact Finset.sum_congr rfl fun c _ => congrArg _ (map_pair S.bV S.pair v.embedding _ _ (S.basis_rat hb i c))

theorem H_posDef (hb : S.HasRatBasis) (hG : (S.gramV.map v.embedding).PosDef) : (S.H.map v.embedding).PosDef := by
  rw [H_map S v hb]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun a ha => ?_
  · ext i j
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply]
    exact wForm_conj _ hG.1 _ _
  · rw [wForm_sum]
    refine lt_of_le_of_ne (wForm_nonneg _ hG.posSemidef _) fun h0 => ha ?_
    have h1 := wForm_eq_zero _ S.wt_pos hG h0.symm
    funext i
    refine Fintype.linearIndependent_iff.1 (coAt_indep S v) a ?_ i
    funext p
    simpa using congrFun (congrFun h1 p.1) p.2

theorem normAt_sq (hb : S.HasRatBasis) (hG : (S.gramV.map v.embedding).PosDef) (x : S.Forms) :
    ((Formalism.HermitianLatticesTheory.normAt S.basis (stdFrame S.H) v x ^ 2 : ℝ) : ℂ) =
      wForm S.wt (S.gramV.map v.embedding) (coAt S v (x : S.Cl → S.V)) (coAt S v (x : S.Cl → S.V)) := by
  have hm := (frameOfSpec _ _ (H_posDef S v hb hG)).2
  have h1 := wForm_sum S.wt (S.gramV.map v.embedding) (fun i => coAt S v (S.basis i : S.Cl → S.V))
    (Formalism.HermitianLatticesTheory.vecAt S.basis v x) (Formalism.HermitianLatticesTheory.vecAt S.basis v x)
  rw [← H_map S v hb, ← hm, metOf, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec] at h1
  rw [coAt_sum S v x]
  refine Eq.trans ?_ h1
  rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_pow, ← Complex.conj_mul']
  rfl

variable (T : GSD K) (h : T.Ok) (hr : ∀ (g : T.G) i j, T.bV.repr (T.ρ g (T.bV j)) i ∈ cmMax K)


include hr in
theorem isFormsOf_toH (hG : ∀ v : InfinitePlace K, (T.gramV.map v.embedding).PosDef) (N : Submodule (𝓞 K) T.EqFun) :
    IsFormsOf T h N (T.toH h N) (LinearEquiv.refl _ _) := by
  refine ⟨fun _ => Iff.rfl, fun v (x : T.EqFun) => ?_⟩
  exact (normAt_sq (T.toCSD h) v (FormsDescent.hasRatBasis_of_act _ fun c γ => hr γ.1) (hG v) (T.res h x)).trans
    (ipAt_eq T h v x x).symm


include h hr in
theorem pairAt_rho (g : T.G) (x : T.V) : T.pairAt v (T.ρ g x) (T.ρ g x) = T.pairAt v x x := by
  let u : T.ιV → Unit → T.ιV → ℂ := fun k _ i => v.embedding (T.bV.repr (T.ρ g (T.bV k)) i)
  have h1 := wForm_sum (fun _ => 1) (T.gramV.map v.embedding) u (fun i => v.embedding (T.bV.repr x i))
    (fun i => v.embedding (T.bV.repr x i))
  have e1 : (Matrix.of fun i j => wForm (fun _ => 1) (T.gramV.map v.embedding) (u i) (u j)) = T.gramV.map v.embedding := by
    ext i j
    simp only [Matrix.of_apply, wForm, Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, inv_one, one_mul]
    refine (map_pair T.bV T.pair v.embedding _ _ fun k => hr g k i).symm.trans ?_
    rw [h.inv]
    rfl
  have e2 : (∑ i, v.embedding (T.bV.repr x i) • u i) = fun _ i => v.embedding (T.bV.repr (T.ρ g x) i) := by
    funext c k
    conv_rhs => rw [← T.bV.sum_repr x]

    simp only [u, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_eq_mul]
    simp
  rw [e1, e2] at h1
  rw [pairAt_eq, pairAt_eq, h1]
  simp only [wForm, Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, inv_one, one_mul]


end Metric

end GlobalTheory.PeriodOnStep
end
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.classNumber_finite_and_genusMass : ∀ D : D7, ClassFin D ∧ ClassMass D := by
  first | exact @GlobalTheory.ClassNumberMass.classFin_and_classMass | exact GlobalTheory.ClassNumberMass.classFin_and_classMass | (intros; apply GlobalTheory.ClassNumberMass.classFin_and_classMass <;> assumption)
end
