module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle984
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle988
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle030
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle535
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle987
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedFiniteDatumFourierExpansionChainless
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle906
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralLatticeUnramifiedDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle822
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle823
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle059
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ScaleInt

theorem exists_prime_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 K) ∈ la.asIdeal := by
  have : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot la.asIdeal la.ne_bot
  have : la.asIdeal.IsMaximal := la.isMaximal
  let _ : Field (𝓞 K ⧸ la.asIdeal) := Ideal.Quotient.field _
  refine ⟨ringChar (𝓞 K ⧸ la.asIdeal), CharP.char_is_prime (𝓞 K ⧸ la.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem exists_avoid {K : Type} [Field K] [NumberField K] (q : Ideal (𝓞 K)) (hq : q.IsPrime)
    (s : Finset (HeightOneSpectrum (𝓞 K))) (hs : ∀ p ∈ s, p.asIdeal ≠ q) (N : HeightOneSpectrum (𝓞 K) → ℕ) :
    ∃ t : 𝓞 K, t ∉ q ∧ ∀ p ∈ s, t ∈ p.asIdeal ^ N p := by
  have hle : ¬ (s.prod fun p => p.asIdeal ^ N p) ≤ q := by
    rw [hq.prod_le]
    rintro ⟨p, hp, hpq⟩
    rcases Nat.eq_zero_or_pos (N p) with h0 | hpos
    · rw [h0, pow_zero, Ideal.one_eq_top, top_le_iff] at hpq
      exact hq.ne_top hpq
    · have h1 : p.asIdeal ≤ q := hq.le_of_pow_le hpq
      exact hs p hp (p.isMaximal.eq_of_le hq.ne_top h1)
  obtain ⟨t, ht, htq⟩ := SetLike.not_le_iff_exists.1 hle
  exact ⟨t, htq, fun p hp => (Ideal.prod_le_inf.trans (Finset.inf_le hp)) ht⟩

theorem le_vLa_of_mem {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) {t : 𝓞 K} (n : ℕ)
    (ht : t ∈ p.asIdeal ^ n) (ht0 : t ≠ 0) : (n : ℤ) ≤ vLa p (t : K) := by
  have h := (p.intValuation_le_pow_iff_mem t n).2 ht
  have hne : p.intValuation t ≠ 0 := HeightOneSpectrum.intValuation_ne_zero p t ht0
  have e : p.valuation K (t : K) = p.intValuation t := p.valuation_of_algebraMap t
  unfold vLa
  rw [e]
  have := (WithZero.log_le_log hne (by simp)).2 h
  simp at this
  omega

theorem vLa_eq_zero_of_not_mem {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) {t : 𝓞 K}
    (ht : t ∉ p.asIdeal) : vLa p (t : K) = 0 := by
  unfold vLa
  rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem p).mpr ht, WithZero.log_one, neg_zero]

end GlobalTheory.ScaleInt

namespace GlobalTheory.ScaleInt



theorem smul_mem_baseInt : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)), κ.LastPos →
    ∀ (q : Ideal (𝓞 T.Q.c.F)), q.IsPrime → ∀ (P : Set (HeightOneSpectrum (𝓞 T.Q.c.F))), P.Finite →
    ∀ ψ ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n {p | p.asIdeal = q},
      ∃ t : 𝓞 T.Q.c.F, t ∉ q ∧ T.σ₀ (t : T.Q.c.F) • ψ ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n P := by
  intro D T hT i κ hκ q hq P hP ψ hψ
  obtain ⟨f, ⟨hfs, hfh, hfv⟩, rfl⟩ := hψ
  have hj : InR D ((i : ℕ) + 1) := inR i
  have hcusp : f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.U ((i : ℕ) + 1)) (wtA κ) κ.n := GlobalTheory.T.mem_cuspForms_allEmbeddings_of_inclusion_reading D T hT _ hj κ hκ f hfs hfh
  have hbd : ∀ p : HeightOneSpectrum (𝓞 T.Q.c.F), ∃ κ' : T.Q.c.F, κ' ≠ 0 ∧
      GlobalTheory.GoodPts.BddAll (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p κ' f := by
    intro p
    obtain ⟨pr, hpr, hmem⟩ := exists_prime_mem p
    exact GlobalTheory.CuspBound.exists_bddAll_cusp _ _ _ _ _ _ _ (T.U ((i : ℕ) + 1)) (hT.unf _ hj) p pr hpr hmem
      (goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne pr hpr) _ _ f
      (dom_wtA κ) hcusp
  choose κ' hκ0 hκb using hbd
  obtain ⟨t, htq, htm⟩ := exists_avoid q hq (hP.toFinset.filter fun p => p.asIdeal ≠ q)
    (fun p hp => (Finset.mem_filter.1 hp).2) (fun p => (vLa p (κ' p)).toNat)
  have ht0 : t ≠ 0 := fun h => htq (h ▸ q.zero_mem)
  have htK : (t : T.Q.c.F) ≠ 0 := by exact_mod_cast ht0
  refine ⟨t, htq, (t : T.Q.c.F) • f, ⟨(sec _ _ _ _).smul_mem _ hfs, ?_, ?_⟩, ?_⟩
  · rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ hfh
  · intro la hla v hv
    have hV := isVal_valSet la v hv
    rw [hV.smul _ _ htK]
    by_cases hlq : la.asIdeal = q
    · have h0 : vAdd la (t : T.Q.c.F) = 0 := vLa_eq_zero_of_not_mem la (hlq ▸ htq)
      rw [h0]
      simpa using hfv la hlq v hv
    · have hmem : la ∈ hP.toFinset.filter fun p => p.asIdeal ≠ q :=
        Finset.mem_filter.2 ⟨hP.mem_toFinset.2 hla, hlq⟩
      have hge : (vLa la (κ' la) : ℤ) ≤ vAdd la (t : T.Q.c.F) :=
        (Int.self_le_toNat _).trans (le_vLa_of_mem la _ (htm la hmem) ht0)
      obtain ⟨y, rfl⟩ := hv
      have hb := (GlobalTheory.GoodPtsModel.bddAll_iff_vAtV (hκ0 la) f).1 (hκb la) y
      exact hb.trans (add_le_add (by exact_mod_cast hge) le_rfl)
  · simp only [CoreJ.phiJ, map_smulₛₗ, LinearMap.map_smul, smul_comm ((lieFac _ _ _ : ℝ) : ℂ)]
    rfl

end GlobalTheory.ScaleInt
end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.CoverPinDom



theorem pin_at {D : D7} (T : CoreJ D) (hL : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ)
    (C : Cover T j σ) (hC : C.IsUnif) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} (hV : T.V j σ = W)
    (hr : W.rank = D.R.r) {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hP : IsPair ψ θ V W χV χW om) (hM : ∀ k, IsMod W hr ((T.U j σ).X k)) {f₀ : WO V W → ℂ}
    (hf₀ : IsThetaFunO ψ V W f₀) {mu : GA D (T.V j σ) → ℂ} (hmu0 : ∀ g, mu g ≠ 0)
    (hunit : ∀ h, IsUnitFr ((T.U j σ).X (T.dict j σ h).1) (T.dict j σ h).2)
    {c₁ : C.U₂.Comp → ℂ} {c₂ : (T.U j σ).Comp → ℂ}
    (h₁ : CcIs θ V W hr C.U₂ (castDict hV C.dict₂) (castDict hV mu) (T.x₀ j σ) om f₀ c₁)
    (h₂ : CcIs θ V W hr (T.U j σ) (castDict hV (T.dict j σ)) (castDict hV mu) (T.x₀ j σ) om f₀ c₂)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (hf : f ∈ sec (T.Q.Xo j) T.Q.c a V.rank)
    (f₂ : Rul C.d.Xo₂ C.d.c₂) (hf₂ : f₂ ∈ sec C.d.Xo₂ C.d.c₂ a V.rank) (hp : C.IsPull f f₂) (g : GA D (T.V j σ)) :
    c₁ (C.dict₂ g).1 * rdU C.U₂ f₂ (C.dict₂ g).1 (C.dict₂ g).2 =
      c₂ (T.dict j σ g).1 * rdU (T.U j σ) f (T.dict j σ g).1 (T.dict j σ g).2 := by
  subst hV
  change CcIs θ V (T.V j σ) hr C.U₂ C.dict₂ mu (T.x₀ j σ) om f₀ c₁ at h₁
  change CcIs θ V (T.V j σ) hr (T.U j σ) (T.dict j σ) mu (T.x₀ j σ) om f₀ c₂ at h₂

  have hθ := hP.inf
  have hC₀ := hC
  have hU₁ := hL.unf j hj σ hσ
  have hU₂ : IsUnf C.U₂ := hC.2.2.2.1
  obtain ⟨_, _, -, hd⟩ := hL.dictU j hj σ hσ
  have hdom₁ : ∀ h, (T.dict j σ h).2 ∈ ((T.U j σ).X (T.dict j σ h).1).dom := hd.2.2.2.1
  obtain ⟨hr₁, g₁, e₁, F₁, ik₁, φ₁, th₁, -, -, hth₁, -, hd₁⟩ := hL.adPin j hj σ hσ
  obtain ⟨-, -, -, -, hdom₂, hr₂, g₂, e₂, F₂, ik₂, φ₂, th₂, hW₂, hth₂, -, hd₂⟩ := hC
  obtain ⟨hr₀, hW₁⟩ := hL.modelW j hj σ hσ
  obtain ⟨γ₁, hγ₁, hL₁, -, hq₁⟩ := hd₁ g
  obtain ⟨γ₂, hγ₂, hL₂, -, hq₂⟩ := hd₂ g
  obtain ⟨δ, hl, hi, hfδ⟩ := GlobalTheory.CoverFrameMove.move (T.V j σ) hr₁ g γ₁ γ₂ hγ₁ hγ₂ _ _ _ _ (hW₁ (T.dict j σ g).1).1 (hW₂ (C.dict₂ g).1).1 hL₁ hL₂
  have hfr : ∀ (τ : D.host.E →+* ℂ) (t₂ : τ ∈ (C.U₂.X (C.dict₂ g).1).Ψ) (t₁ : τ ∈ ((T.U j σ).X (T.dict j σ g).1).Ψ),
      mat (T.dict j σ g).2 ⟨τ, t₁⟩ = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ g).2 ⟨τ, t₂⟩ := by
    intro τ t₂ t₁
    have e₂' := hq₂ ⟨τ, t₂⟩
    have e₁' := hq₁ ⟨τ, t₁⟩
    rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at e₂'
    rw [e₁', e₂']
    exact hfδ τ _ (hth₁ _ ⟨τ, t₁⟩) _
  have hΨ₁ : ∀ k, ∀ τ ∈ ((T.U j σ).X k).Ψ, ∃ ρ, τ = tauE D ρ := fun k τ hτ => ((hM k).psi τ).1 hτ
  have hΨ₂ : ∀ k, ∀ τ ∈ (C.U₂.X k).Ψ, ∃ ρ, τ = tauE D ρ := fun k τ hτ =>
    hΨ₁ (T.dict j σ g).1 τ (((hU₁.2.1 _).2 τ).2 (((hU₂.2.1 k).2 τ).1 hτ))
  have hat₁ : AtComp θ (T.V j σ) hr (T.U j σ).X (T.dict j σ) (T.x₀ j σ) g γ₁ := by
    refine ⟨hγ₁, ?_, ?_⟩
    · apply SetLike.coe_injective
      rw [hL₁, latR, Submodule.map_coe]
      rfl
    · funext τ
      have := hq₁ τ
      rw [← GlobalTheory.AdTh.CcModel.realM_mt hθ _ (γ₁ * g) τ.1 (hΨ₁ _ _ τ.2) _ (hth₁ _ τ)] at this
      exact this
  have hat₂ : AtComp θ (T.V j σ) hr C.U₂.X C.dict₂ (T.x₀ j σ) g γ₂ := by
    refine ⟨hγ₂, ?_, ?_⟩
    · apply SetLike.coe_injective
      rw [hL₂, latR, Submodule.map_coe]
      rfl
    · funext τ
      have := hq₂ τ
      rw [← GlobalTheory.AdTh.CcModel.realM_mt hθ _ (γ₂ * g) τ.1 (hΨ₂ _ _ τ.2) _ (hth₂ _ τ)] at this
      exact this
  have hrm : ∀ τ ∈ ((T.U j σ).X (T.dict j σ g).1).Ψ, Matrix.reindex (finCongr hr) (finCongr hr)
      (realM θ (Formalism.L2.Theta.mt (T.V j σ) (γ₁ * γ₂⁻¹)) τ) = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ := by
    intro τ t₁
    have hth := hth₁ _ ⟨τ, t₁⟩
    rw [GlobalTheory.AdTh.CcModel.realM_mt hθ _ _ τ (hΨ₁ _ _ t₁) _ hth]
    generalize th₁ (T.dict j σ g).1 ⟨τ, t₁⟩ = th at hth ⊢
    have hmul : ∀ a b : GA D (T.V j σ), archM (T.V j σ) th (a * b) = archM _ th a * archM _ th b := fun a b => by
      rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]
    have hone : archM (T.V j σ) th 1 = 1 := by
      rw [archM, map_one, Units.val_one, Matrix.map_one] <;> simp
    have hre : ∀ A B : Matrix (Fin (T.V j σ).rank) (Fin (T.V j σ).rank) ℂ,
        Matrix.reindex (finCongr hr) (finCongr hr) (A * B) =
          Matrix.reindex (finCongr hr) (finCongr hr) A * Matrix.reindex (finCongr hr) (finCongr hr) B := fun A B => by
      simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    have e1 := hfδ τ th hth 1
    rw [Matrix.mul_one, Matrix.mul_one] at e1
    rw [show γ₁ * g = γ₁ * γ₂⁻¹ * (γ₂ * g) by group, hmul, hre] at e1
    have e3 : Matrix.reindex (finCongr hr) (finCongr hr) (archM (T.V j σ) th (γ₂ * g)) *
        Matrix.reindex (finCongr hr) (finCongr hr) (archM (T.V j σ) th (γ₂ * g)⁻¹) = 1 := by
      rw [← hre, ← hmul, mul_inv_cancel, hone]
      simp
    calc _ = Matrix.reindex (finCongr hr) (finCongr hr) (archM (T.V j σ) th (γ₁ * γ₂⁻¹)) *
          (Matrix.reindex (finCongr hr) (finCongr hr) (archM (T.V j σ) th (γ₂ * g)) *
            Matrix.reindex (finCongr hr) (finCongr hr) (archM (T.V j σ) th (γ₂ * g)⁻¹)) := by rw [e3, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e1, Matrix.mul_assoc, e3, Matrix.mul_one]
  have hm2 : ∀ a b : GA D (T.V j σ), om (1, a * b) = om (1, a) * om (1, b) := fun a b => by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  have hF : ∀ w, om (1, γ₁ * g) f₀ (actO V (T.V j σ) 1 (γ₁ * γ₂⁻¹) w) = om (1, γ₂ * g) f₀ w := fun w => by
    rw [show γ₁ * g = γ₁ * γ₂⁻¹ * (γ₂ * g) by group, hm2, Module.End.mul_apply]
    exact GlobalTheory.WeilRat.om_rat_actO D ψ hP.weil.std V (T.V j σ) χV χW om hP.weil 1 (one_mem _) _
      (mul_mem hγ₁ (inv_mem hγ₂)) _ (hP.weil.om_pres _ _ hf₀) w
  have key := GlobalTheory.T.vacuumReadingConstants_levelCover_relate_core D T hL j hj σ hσ C hC₀ ψ θ V χV χW om hP hr hM g δ hl hi hfr (γ₁ * γ₂⁻¹) hrm (hdom₁ g) (hdom₂ g)
    (hunit g) (om (1, γ₂ * g) f₀) (om (1, γ₁ * g) f₀) (c₁ (C.dict₂ g).1 * mu g) (c₂ (T.dict j σ g).1 * mu g)
    (h₁.2 g γ₂ hat₂ (hdom₂ g)) (h₂.2 g γ₁ hat₁ (hdom₁ g)) hF a f hf f₂ hf₂ hp
  apply mul_left_cancel₀ (hmu0 g)
  linear_combination key



theorem isPinned_inv_mul : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ ph : ℂ, ‖ph‖ = 1 → BaseCc T R i hV ph → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → ∀ cc : C.U₂.Comp → ℂ, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) C.U₂ (castDict hV C.dict₂) (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) (T.x₀ ((i : ℕ) + 1) T.σ₀) (R.ωP i A.μ0) (R.vacP i) cc → ∀ a, Dom a (κ i).n → ({ C with cc₂ := fun k => ph⁻¹ * cc k } : Cover T ((i : ℕ) + 1) T.σ₀).IsPinned a (κ i).n := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hlev hgrp hfam hmods hthP ht i hS hV ph hph hbase C hC cc hcc a ha
  have hC3 : GlobalTheory.Hk3.CoreNoChain R F := ⟨hlev, hgrp, hfam, hmods, hthP⟩
  have hj : InR D ((i : ℕ) + 1) := inR i
  have hσ : GoodEmb T.Q.c T.σ₀ := T.good_σ₀
  have hmod := GlobalTheory.AdTh.models_at_record_core_nc D G Pl0 T0 A T R F κ v₀ hC3 ht i T.σ₀ rfl
  have hP := (GlobalTheory.AdTh.RecPairCore.isPair_record_core_nc D G Pl0 T0 A T.Q.c.F R F hC3 i A.μ0 hS).1
  have hf₀ := (hthP.vP i A.μ0).1.2.theta
  have hmu0 : ∀ g, T.mu ((i : ℕ) + 1) T.σ₀ g ≠ 0 := fun g =>
    norm_ne_zero_iff.1 (((hL.muVal _ hj _ hσ).norm g).trans_ne one_ne_zero)
  have hunit := (hL.muUnit _ hj _ hσ).2.2.2
  have hph0 : ph ≠ 0 := norm_ne_zero_iff.1 (by rw [hph]; exact one_ne_zero)
  refine ⟨fun k => ?_, fun f hf f₂ hf₂ hp => ?_⟩
  · show ‖ph⁻¹ * cc k‖ = 1
    rw [norm_mul, norm_inv, hph, hcc.norm k, inv_one, one_mul]
  · funext g
    have hn : (κ i).n = (Vc D i).rank := (hmod (T.dict _ _ g).1).2.2.2.2.2.2.2.2.2.2.2.1
    rw [hn] at hf hf₂
    have key := GlobalTheory.CoverPinDom.pin_at T hL _ hj _ hσ C hC hV (rank_Wc i) hP (fun k => (hmod k).1) hf₀ hmu0 hunit hcc
      hbase a f hf f₂ hf₂ hp g
    show Cover.rd _ a f₂ g = T.phiJ _ _ a f g
    simp only [Cover.rd, CoreJ.phiJ, Pi.smul_apply, smul_eq_mul, adel_muPin] at key ⊢
    have hinv : ph⁻¹ * ph = 1 := inv_mul_cancel₀ hph0
    linear_combination (↑(lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a) * ph⁻¹ * T.mu ((i : ℕ) + 1) T.σ₀ g) * key +
      (↑(lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a) * T.cE ((i : ℕ) + 1) T.σ₀ (T.dict ((i : ℕ) + 1) T.σ₀ g).1 *
        T.mu ((i : ℕ) + 1) T.σ₀ g * rdU (T.U ((i : ℕ) + 1) T.σ₀) f (T.dict ((i : ℕ) + 1) T.σ₀ g).1
          (T.dict ((i : ℕ) + 1) T.σ₀ g).2) * hinv

end GlobalTheory.CoverPinDom
end
end

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct



namespace GlobalTheory.GeoTie.BallDescent

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Sum

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀) {i : D.ntw.Tw} {iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]} {b : Bool}
  (j : Fin D.R.m)

theorem valC_cuspOf_sum (z : FrC YS iC b ((j : ℕ) + 1)) {ι : Type} (s : Finset ι) (g : ι → NX.FmK S ((j : ℕ) + 1)) :
    valC z (cuspOf YS fw j (∑ t ∈ s, g t) : T0.R ((j : ℕ) + 1)) =
      ∑ t ∈ s, valC z (cuspOf YS fw j (g t) : T0.R ((j : ℕ) + 1)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, map_zero, ZeroMemClass.coe_zero, valC_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, map_add (f := _), Submodule.coe_add, valC_add, ih]

end Sum

theorem ball_descent : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), (∀ f : NX.FmK S ((j : ℕ) + 1), ∃ c : S.Ks, c ≠ 0 ∧ c • f ∈ locBall YS fw iC b j) → ∀ (F' : Type) [Field F'] [NumberField F'] [Algebra S.Ks F'] (φ' : F' →+* ℂ_[D.ntw.l i]), (∀ a, φ' (algebraMap S.Ks F' a) = embS S iC b a) → (∀ a : S.Ks, vLa (placeAt φ') (algebraMap S.Ks F' a) = vLa (placeAt (embS S iC b)) a) → ∀ (n : ℕ) (a : Fin n → F') (f : Fin n → NX.FmK S ((j : ℕ) + 1)), (∀ z : Pts YS iC b ((j : ℕ) + 1), ‖∑ s, φ' (a s) * valC z.1 (cuspOf YS fw j (f s) : T0.R ((j : ℕ) + 1))‖ ≤ 1) → ∃ (m : ℕ) (β : Fin m → F') (g : Fin m → NX.FmK S ((j : ℕ) + 1)), (∀ t, ‖φ' (β t)‖ ≤ 1) ∧ (∀ t, g t ∈ locBall YS fw iC b j) ∧ ∑ s, a s ⊗ₜ[S.Ks] f s = ∑ t, β t ⊗ₜ[S.Ks] g t := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _hiC b j hball F' _ _ _ φ' hφ' hv n a f hz
  have := GlobalTheory.SupDescent.liesOver (K := S.Ks) (K' := F') (la := placeAt (embS S iC b)) (la' := placeAt φ') hv
  obtain ⟨d, bb, hb1, hb2⟩ := GlobalTheory.SupDescent.exists_residue_basis (la := placeAt (embS S iC b)) (la' := placeAt φ')
  choose c hc0 hcB using fun s => hball (f s)
  choose x ρ hρ hx using fun s => GlobalTheory.SupDescent.exists_approx (K := S.Ks) (K' := F') hv hb2 (a s) (hc0 s)
  let F : Fin d → NX.FmK S ((j : ℕ) + 1) := fun t => ∑ s, x s t • f s
  have hmem : ∀ g : NX.FmK S ((j : ℕ) + 1), (cuspOf YS fw j g : T0.R ((j : ℕ) + 1)) ∈
      sec (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (wtA (κ j)) (κ j).n := cuspOf_mem_sec YS fw j
  have hF : ∀ t, F t ∈ locBall YS fw iC b j := by
    intro t z
    obtain ⟨T, io, k, hR, y, u, hT, hu, hval⟩ := PtC.exists_valC z (wtA (κ j)) (κ j).n
    rw [hval _ (hmem _), norm_mul, hu, one_mul]
    let io' : S.Ks →+* T.Fr := io.comp (eKs YS).toRingHom
    have hR' : IsReading (embS S iC b) T io' k :=
      ⟨fun a => (hR.comp (eKs YS a)).trans (embC_eKs YS iC b a), hR.int⟩
    obtain ⟨e, ho⟩ := GlobalTheory.ReadingOver.overLa_placeAt_of_isReading (embS S iC b) hR'
    refine (hR.int _).2 ?_
    refine GlobalTheory.SupDescent.inV_of_forall_emb (K := S.Ks) (K' := F') hb1 hT ho
      (fun t => evI y (cuspOf YS fw j (F t) : T0.R ((j : ℕ) + 1))) ?_ t
    intro T' i e' σ e'' he' hi hT' hσ ho'
    obtain ⟨y₁, ψ, hψ, hmap⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange _ _ _ _ _ _ T T' io y i e' he' hi
    obtain ⟨k', hk'⟩ := GlobalTheory.GeoTie.ReadExist.exists_isReading _ F' φ' T' σ e'' ho' hT'
    have hR₁ : IsReading (embC YS iC b) T' (i.comp io) k' := by
      refine ⟨fun a => ?_, hk'.int⟩
      obtain ⟨a0, rfl⟩ := (eKs YS).surjective a
      rw [embC_eKs, ← hφ' a0, ← hk'.comp, hσ a0]
      rfl
    obtain ⟨z', hz'⟩ := PtC.exists_of_reading hR₁ y₁ hT'
    have h4 : ∀ g : NX.FmK S ((j : ℕ) + 1),
        k' (i (evI y (cuspOf YS fw j g : T0.R ((j : ℕ) + 1)))) = valC z'.1 (cuspOf YS fw j g : T0.R ((j : ℕ) + 1)) := by
      intro g
      have h5 : i (evI y (cuspOf YS fw j g : T0.R ((j : ℕ) + 1))) = evI y₁ (cuspOf YS fw j g : T0.R ((j : ℕ) + 1)) := by
        letI := io.toAlgebra
        letI := (i.comp io).toAlgebra
        exact (DFunLike.congr_fun hψ _).symm.trans (GlobalTheory.FlagTan.evR_frMap (hmem g).1 hmap).symm
      rw [h5, hz' _ _ _ (hmem g)]
    refine (hk'.int _).1 ?_

    rw [map_sum]
    simp only [map_mul, hk'.comp, h4]
    have hid : ∑ t, φ' (bb t : F') * valC z'.1 (cuspOf YS fw j (F t) : T0.R ((j : ℕ) + 1)) =
        ∑ s, φ' (a s) * valC z'.1 (cuspOf YS fw j (f s) : T0.R ((j : ℕ) + 1)) -
          ∑ s, φ' (ρ s) * valC z'.1 (cuspOf YS fw j (c s • f s) : T0.R ((j : ℕ) + 1)) := by
      rw [eq_sub_iff_add_eq]
      simp only [F, valC_cuspOf_sum YS fw j, valC_cuspOf_smul YS fw j, Finset.mul_sum]
      rw [Finset.sum_comm, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hx s]

      simp only [map_add (f := _), map_sum, map_mul, hφ', Finset.sum_mul, add_mul]
      congr 1
      · exact Finset.sum_congr rfl fun t _ => by ring
      · ring
    rw [hid]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hz z') ?_)
    rw [norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun s _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one φ' (hρ s)) (norm_nonneg _) (hcB s z')
  refine ⟨d + n, Fin.append (fun t => (bb t : F')) ρ, Fin.append F fun s => c s • f s, fun t => ?_, fun t => ?_, ?_⟩
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) t
    · rw [Fin.append_left]; exact norm_int_le_one φ' (bb t)
    · rw [Fin.append_right]; exact GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one φ' (hρ t)
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) t
    · rw [Fin.append_left]; exact hF t
    · rw [Fin.append_right]; exact hcB t
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have e : ∀ s, a s = ∑ t, x s t • (bb t : F') + c s • ρ s := fun s => by
      rw [hx s]; simp only [Algebra.smul_def]; rw [mul_comm (algebraMap _ _ (c s))]
    have h1 : ∀ t s, (bb t : F') ⊗ₜ[S.Ks] (x s t • f s) = (x s t • (bb t : F')) ⊗ₜ[S.Ks] f s :=
      fun t s => (TensorProduct.smul_tmul _ _ _).symm
    have h2 : ∀ s, ρ s ⊗ₜ[S.Ks] (c s • f s) = (c s • ρ s) ⊗ₜ[S.Ks] f s := fun s => (TensorProduct.smul_tmul _ _ _).symm
    simp only [F, TensorProduct.tmul_sum, h1, h2]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← TensorProduct.sum_tmul, ← TensorProduct.add_tmul, ← e s]

end GlobalTheory.GeoTie.BallDescent
end
end
