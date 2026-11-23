module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle231
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPermOfCardFalse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle056
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle566
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle340
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle337
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SignedHC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepRows

theorem exists_dsModel_cart {D : D7} (hDS : GlobalTheory.Published.DiscreteSeriesUpqExists) {V : HSp D} (hV : V.SigOK)
    (S : D.what₂.Tau → SPar) (O C : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hS : ∀ τ, SignedHC.IsRegular (S τ)) (hc : ∀ τ, (S τ).card = V.rank)
    (hm : ∀ τ, SignedHC.nMinus (S τ) = (V.sig (tauE D τ)).2)
    (hP : ∀ τ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam)
    (h : ∀ τ, ∃ ε : Fin V.rank → Bool, (O τ)ᴴ * gramAt D V τ * O τ = Formalism.REAL.Jm ε ∧ C τ * O τ = O τ * Formalism.REAL.Jm ε) :
    ∃ M : DSModel V S, cart M = C := by

  have hperm : ∀ τ, ∃ σ : Equiv.Perm (Fin V.rank), ∃ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε ∧
      ((O τ).submatrix id σ)ᴴ * gramAt D V τ * (O τ).submatrix id σ = Formalism.REAL.Jm ε ∧
      C τ * (O τ).submatrix id σ = (O τ).submatrix id σ * Formalism.REAL.Jm ε :=
    fun τ => GlobalTheory.GridJoin.exists_perm_onb hV τ (hS τ) (hc τ) (hm τ) (h τ)
  choose σ lam ε hEn hGr hCa using hperm
  obtain ⟨M, hMc, -⟩ := GlobalTheory.dsModel_of_onb_cart D hDS V S (fun τ => (O τ).submatrix id (σ τ)) C
    (fun τ => ⟨lam τ, ε τ, hEn τ, hP τ (lam τ) (ε τ) (hEn τ), hGr τ⟩) (fun τ => ⟨ε τ, hGr τ, hCa τ⟩)
  exact ⟨M, hMc⟩

private theorem exists_int_eq_half_add_of_mem_parPi (G : GlobalTheory.SignedHC.GridData) (hs : Odd G.s) (i : ℕ) (x : ℚ) (b : Bool)
    (hx : (x, b) ∈ G.parPi i) : ∃ z : ℤ, x = 1 / 2 + z := by
  rcases GlobalTheory.SignedHC.GridData.mem_parPi.1 hx with ⟨l, -, hl⟩ | ⟨hc, -⟩ | ⟨l, -, -, hl, -⟩
  · simp only [Prod.mk.injEq] at hl
    refine ⟨G.v 2 + ((G.m : ℤ) + 1 - l) * G.ga, ?_⟩
    rw [hl.1, GlobalTheory.SignedHC.GridData.a]
    push_cast
    ring
  · dsimp only at hc
    obtain ⟨j, -, -, hj⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 hc
    refine ⟨G.v j - 1, ?_⟩
    rw [hj, GlobalTheory.SignedHC.GridData.vHalf]
    push_cast
    ring
  · dsimp only at hl
    obtain ⟨w, hw⟩ := hs
    obtain ⟨z, hz⟩ := GlobalTheory.SignedHC.inCoset_block _ _ x hl
    refine ⟨G.cen l + w + z, ?_⟩
    have hlen : ((G.s - 1 : ℕ) : ℚ) = 2 * w := by
      rw [hw, Nat.add_sub_cancel]; push_cast; ring
    rw [hz, hlen]
    push_cast
    ring

theorem isHCParam_parPi (D : D7) (C : ℝ) (i : ℕ) (τ : D.what₂.Tau) {n : ℕ} (lam : Fin n → ℝ) (ε : Fin n → Bool)
    (hn : n = rankP D i) (hE : IsEnum ((num D C τ).parPi i) lam ε) : Formalism.QuantumDeterminants.IsHCParam lam := by
  obtain ⟨hanti, q, hq, hS⟩ := hE
  refine ⟨hanti, fun a => ?_⟩
  have hmem : (q a, ε a) ∈ (num D C τ).parPi i := by
    rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
  obtain ⟨z, hz⟩ := exists_int_eq_half_add_of_mem_parPi (num D C τ) (odd_sLen D) i (q a) (ε a) hmem
  obtain ⟨k, hk⟩ := even_rankP D i
  refine ⟨z - k + 1, ?_⟩
  rw [hq a, hz, hn, hk]
  push_cast
  ring

theorem coreModels_of_upq (hDS : GlobalTheory.Published.DiscreteSeriesUpqExists) : CoreModels := by
  intro D _ T L μ0 _ sc G W M _ i hi
  have hin : (Node.core i).InRange D.R.m := hi
  obtain ⟨hrank, hsig, hsg, -⟩ := G.isV hin (fun j h => by cases h)
  have hg : 0 < (gap D sc.cGap) := lt_of_le_of_lt (Nat.zero_le _) (sLen_lt_gap D sc.cGap)
  have hs1 : 1 ≤ sLen D := by unfold sLen; omega
  refine exists_dsModel_cart hDS hsig (Node.par D sc.cGap (.core i)) (W.onb (.core i)) (W.cart (.core i))
    (fun τ => ?_) (fun τ => ?_) (fun τ => ?_) (fun τ lam ε hE => ?_) (W.onb_is (.core i) hin)
  · exact GlobalTheory.PiCounts.isRegular_parPi (num_nearMid D sc.cGap τ) hs1 (sLen_lt_gap D sc.cGap) hi
  · exact (GlobalTheory.PiCounts.card_parPi (num_nearMid D sc.cGap τ) hs1 (sLen_lt_gap D sc.cGap) hi).trans
      ((num_ranks D sc.cGap τ i 0).2.1.trans hrank.symm)
  · show nMinus ((num D sc.cGap τ).parPi i) = _
    rw [GlobalTheory.PiCounts.nMinus_parPi hg i, hsg (tauE D τ)]
    rfl
  · exact isHCParam_parPi D sc.cGap i τ lam ε hrank hE

end GlobalTheory.SepRows

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SplitSign

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conj_conj {σ : E →ₐ[F] E} (hc : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply τ.injective
  rw [hc.2.2.2 τ, hc.2.2.2 τ, star_star]

theorem exists_anti_unit {σ : E →ₐ[F] E} (hc : IsCMExt F E σ) {v : Pl (F := F)} (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) :
    ∃ (τ : E →ₐ[F] Fv F v) (δ : 𝓞 E), σ (δ : E) = -(δ : E) ∧ Valued.v (τ (δ : E)) = 1 := by
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := hv
  have hPv : P.under (𝓞 F) = v := HeightOneSpectrum.ext hP
  obtain ⟨τ, hτ⟩ := SplitChart.exists_splitPrime_eq hc ⟨P, Q, hPQ, hP, hQ⟩ hPv
  obtain ⟨w', hne, -, -, -, hw'⟩ := SplitChart.exists_conj_place hc (splitPrime_under τ) ⟨P, Q, hPQ, hP, hQ⟩
  have hmax : (splitPrime τ).asIdeal.IsMaximal := (splitPrime τ).isMaximal
  have hmax' : w'.asIdeal.IsMaximal := w'.isMaximal
  have hnle : ¬ (splitPrime τ).asIdeal ≤ w'.asIdeal := fun hle =>
    hne (HeightOneSpectrum.ext (hmax.eq_of_le hmax'.ne_top hle))
  obtain ⟨θ, hθP, hθw⟩ := Set.not_subset.1 hnle
  set σθ : 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E) θ with hσθ
  have hσθP : σθ ∉ (splitPrime τ).asIdeal := by
    intro h
    apply hθw
    rw [hw']
    exact h
  refine ⟨τ, θ - σθ, ?_, ?_⟩
  · have e : ((σθ : 𝓞 E) : E) = σ (θ : E) := rfl
    push_cast
    rw [map_sub]
    change σ (θ : E) - σ (σ (θ : E)) = -((θ : E) - σ (θ : E))
    rw [conj_conj hc]
    ring
  · have hnot : θ - σθ ∉ (splitPrime τ).asIdeal := by
      intro h
      apply hσθP
      have := (splitPrime τ).asIdeal.sub_mem hθP h
      simpa using this
    rw [mem_splitPrime] at hnot
    exact le_antisymm (apply_coe_mem τ _) (not_lt.1 hnot)

theorem smul_eq_self_of_at {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl (F := F)} {z : M}
    (hz : At (evFin F v) z) : GlobalTheory.LatVac.liftV v 1 • z = z := by
  have h := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h
  exact h.symm

theorem liftV_mul_liftV (v : Pl (F := F)) (a b : Fv F v) :
    GlobalTheory.LatVac.liftV v a * GlobalTheory.LatVac.liftV v b = GlobalTheory.LatVac.liftV v (a * b) := by
  rw [show GlobalTheory.LatVac.liftV v a * GlobalTheory.LatVac.liftV v b = _ from GlobalTheory.EmbChart.atPlace_mul_right v a _]
  show GlobalTheory.LatVac.liftV v (a * evFin F v (GlobalTheory.LatVac.liftV v b)) = _
  rw [GlobalTheory.LatVac.evFin_liftV]

end GlobalTheory.SplitSign


open GlobalTheory.SplitSign in
theorem GlobalTheory.SplitSign.exists_split_sign : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → ∃ c : AE F E, cA σ c = -c ∧ At (evFin F v) c ∧
      (∀ z : AE F E, At (evFin F v) z → c * c * z = z) ∧
      ∀ (d : ℕ) (W : Spc F E d), ∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ σ B hB v hv
  obtain ⟨τ, δ, hσδ, hδv⟩ := exists_anti_unit hB.cm hv
  set s : Fv F v := τ (δ : E) with hs
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hδv
    exact zero_ne_one hδv
  have hsinv : s⁻¹ ∈ v.adicCompletionIntegers F := by
    show Valued.v s⁻¹ ≤ 1
    rw [map_inv₀, hδv, inv_one]
  obtain ⟨f, hf⟩ := SnMass.SkewVol.mem_range_of_cm_fixed hB.cm (x := (δ : E) * δ)
    (by rw [map_mul, hσδ, neg_mul_neg])
  refine ⟨GlobalTheory.LatVac.liftV v s⁻¹ ⊗ₜ[F] (δ : E), ?_, ?_, ?_, ?_⟩
  · rw [cA, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hσδ, TensorProduct.tmul_neg]
  · intro u hu
    rw [TensorProduct.smul_tmul', GlobalTheory.LatVac.at_liftV v s⁻¹ u hu, TensorProduct.zero_tmul]
  · intro z hz
    have hcc : (GlobalTheory.LatVac.liftV v s⁻¹ ⊗ₜ[F] (δ : E)) * (GlobalTheory.LatVac.liftV v s⁻¹ ⊗ₜ[F] (δ : E)) =
        GlobalTheory.LatVac.liftV v 1 • (1 : AE F E) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← hf, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', liftV_mul_liftV, ← map_smul]
      have h1 : f • (s⁻¹ * s⁻¹) = (1 : Fv F v) := by
        rw [Algebra.smul_def, ← AlgHom.commutes τ f, hf, map_mul, ← hs]
        field_simp
      rw [h1, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hcc, smul_mul_assoc, one_mul, smul_eq_self_of_at hz]
  · intro d W z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hav, y, hy, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v s⁻¹ * a, ?_, ?_, δ • y, W.L.smul_mem δ hy, ?_⟩
      · intro u hu
        rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
      · rw [map_mul, GlobalTheory.LatVac.evFin_liftV]
        exact mul_mem hsinv hav
      · funext i
        simp only [Pi.smul_apply, smul_eq_mul, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul', mul_one,
          Algebra.TensorProduct.tmul_mul_tmul]
        rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv GlobalTheory.StepLeft Classical

noncomputable section
namespace GlobalTheory.StepLeft

section Shape
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}


omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem basePt_eq_zero_of_stepVar (y : Matrix n n' k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) : basePt c y r s = 0 := by
  rcases r with r | r <;> rcases s with s | s <;> simp only [Free, Kept, or_false, false_or] at h <;>
    simp only [basePt, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, of_apply]
  rw [if_neg (by omega)]


omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem stepVar_fixed_of_ordL_lt (y : Matrix n n' k) {r t : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hv : ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s))) (hlt : GlobalTheory.DiagVol.ordL c r < GlobalTheory.DiagVol.ordL c t) :
    ¬ (Free (c / 2 + 1) (t, s) ∨ Kept (t, s)) ∧ basePt c y t s = 0 := by
  rcases r with r | r <;> rcases t with t | t <;> rcases s with s | s <;>
    simp only [Free, Kept, GlobalTheory.DiagVol.ordL, Sum.elim_inl, Sum.elim_inr, basePt, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, of_apply, not_or,
      Nat.even_iff, Nat.odd_iff, not_and, true_and, and_true, not_false_eq_true, not_true_eq_false] at hv hlt ⊢
  all_goals first | omega | (refine ⟨⟨by omega, by omega⟩, ?_⟩; rw [if_neg (by omega)]) | (refine ⟨by omega, ?_⟩; rw [if_neg (by omega)]) | skip

end Shape

section Shape2
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}


omit [Fintype n'] [DecidableEq n'] in
theorem unipSub_mul_fixed {u : GL (n ⊕ Fin c) k} (hu : u ∈ GlobalTheory.DiagVol.unipSub (GlobalTheory.DiagVol.ordL c))
    (y : Matrix n n' k) (M : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (hM : ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → M r s = basePt c y r s) :
    ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → (u.val * M) r s = basePt c y r s := by
  intro r s hv
  have hu' : ∀ r t, GlobalTheory.DiagVol.ordL c t ≤ GlobalTheory.DiagVol.ordL c r →
      u.val r t = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r t := hu
  rw [Matrix.mul_apply, Finset.sum_eq_single r]
  · rw [hu' r r le_rfl, Matrix.one_apply_eq, one_mul, hM r s hv]
  · intro t _ htr
    by_cases h : GlobalTheory.DiagVol.ordL c t ≤ GlobalTheory.DiagVol.ordL c r
    · rw [hu' r t h, Matrix.one_apply_ne (Ne.symm htr), zero_mul]
    · obtain ⟨h1, h2⟩ := stepVar_fixed_of_ordL_lt y hv (not_le.1 h)
      rw [hM t s h1, h2, mul_zero]
  · simp


omit [Fintype n'] [DecidableEq n'] in
theorem embX_mul_fixed (κ : GL n k) (y : Matrix n n' k) (M : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (hM : ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → M r s = basePt c y r s) :
    ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) →
      ((embX c κ).val * M) r s = basePt c (κ.val * y) r s := by
  intro r s hv
  have hE : (embX c κ).val = (fromBlocks κ.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) := rfl
  rw [hE, Matrix.mul_apply, Fintype.sum_sum_type]
  rcases r with a | l
  · simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    have hb : ∀ b, M (Sum.inl b) s = basePt c y (Sum.inl b) s := fun b =>
      hM _ _ (by rcases s with s | s <;> simpa only [Free, Kept] using hv)
    simp only [hb]
    rcases s with s | s <;> simp [basePt, Matrix.mul_apply]
  · simp only [fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single l (fun j _ hj => by rw [Matrix.one_apply_ne (Ne.symm hj), zero_mul]) (by simp),
      Matrix.one_apply_eq, one_mul, hM _ _ hv]
    rcases s with s | s <;> simp [basePt]

end Shape2

theorem inv_mul_stepPt_shape : ∀ {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (v : GL (n ⊕ Fin c) k), v ∈ symN k n c → ∀ (κ : GL n k) (x₀ : Matrix n n' k) (e : StepVar n c n' → k), ((v * embX c κ)⁻¹).val * stepPt x₀ e = stepPt ((κ⁻¹).val * x₀) (fun a => (((v * embX c κ)⁻¹).val * stepPt x₀ e : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) a.1.1 a.1.2) := by
  intro k _ n n' _ _ _ _ c v hv κ x₀ e
  have hg : ((v * embX c κ)⁻¹).val = (embX c κ⁻¹).val * (v⁻¹).val := by
    rw [_root_.mul_inv_rev, map_inv, Units.val_mul]
  have hu : v⁻¹ ∈ GlobalTheory.DiagVol.unipSub (GlobalTheory.DiagVol.ordL c) := GlobalTheory.DiagVol.symN_le_unipSub (inv_mem hv)
  have hM : ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → stepPt x₀ e r s = basePt c x₀ r s :=
    fun r s h => by rw [stepPt, Matrix.add_apply, of_apply, dif_neg h, add_zero]
  have hA := embX_mul_fixed κ⁻¹ x₀ _ (unipSub_mul_fixed hu x₀ _ hM)
  have hR : ∀ (y : Matrix n n' k) (e' : StepVar n c n' → k) r s, stepPt y e' r s =
      basePt c y r s + (if h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s) then e' ⟨(r, s), h⟩ else 0) :=
    fun _ _ _ _ => rfl
  ext r s
  by_cases h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)
  · conv_rhs => rw [hR, dif_pos h, basePt_eq_zero_of_stepVar _ h, zero_add]
  · conv_rhs => rw [hR, dif_neg h, add_zero]
    rw [hg, Matrix.mul_assoc, hA r s h]

end GlobalTheory.StepLeft
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.KFinAlg

def tensDeg (F : Type) [Field F] [NumberField F] (P Q R S D : ℕ) : Submodule ℂ (GlobalTheory.RealLift.Tens F P Q R S) :=
  LinearMap.range (PiTensorProduct.map fun _ : InfinitePlace F =>
    (MvPolynomial.restrictTotalDegree (Formalism.BasicNotions.TH.Ix P Q × Formalism.BasicNotions.TH.Ix R S) ℂ D).subtype)

theorem tensDeg_mono {F : Type} [Field F] [NumberField F] {P Q R S D D' : ℕ} (h : D ≤ D') :
    tensDeg F P Q R S D ≤ tensDeg F P Q R S D' := by
  have hi : MvPolynomial.restrictTotalDegree (Formalism.BasicNotions.TH.Ix P Q × Formalism.BasicNotions.TH.Ix R S) ℂ D ≤
      MvPolynomial.restrictTotalDegree _ ℂ D' := fun x hx => by
    rw [MvPolynomial.mem_restrictTotalDegree] at hx ⊢; omega
  rintro _ ⟨t, rfl⟩
  refine ⟨PiTensorProduct.map (fun _ => Submodule.inclusion hi) t, ?_⟩
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  rfl

theorem exists_tensDeg {F : Type} [Field F] [NumberField F] {P Q R S : ℕ} (T : GlobalTheory.RealLift.Tens F P Q R S) :
    ∃ D, T ∈ tensDeg F P Q R S D := by
  classical
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    refine ⟨Finset.univ.sup fun w => (m w).totalDegree, r • PiTensorProduct.tprod ℂ (fun w =>
      (⟨m w, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 (Finset.le_sup (f := fun w => (m w).totalDegree)
        (Finset.mem_univ w))⟩ : MvPolynomial.restrictTotalDegree _ ℂ _)), ?_⟩
    simp [PiTensorProduct.map_tprod]
  | add x y hx hy =>
    obtain ⟨D₁, h₁⟩ := hx
    obtain ⟨D₂, h₂⟩ := hy
    exact ⟨max D₁ D₂, Submodule.add_mem _ (tensDeg_mono (le_max_left _ _) h₁) (tensDeg_mono (le_max_right _ _) h₂)⟩

theorem exp_stable {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (hU : GlobalTheory.RealLift.IsExp L U)
    (N : Submodule ℂ V) (hN : ∀ y ∈ N, L y ∈ N) : ∀ y ∈ N, U y ∈ N := by
  intro y hy
  by_contra hne
  obtain ⟨l, hl1, hl2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hne inferInstance
  have hpow : ∀ m : ℕ, (L ^ m) y ∈ N := by
    intro m
    induction m with
    | zero => simpa using hy
    | succ m ih => rw [pow_succ', Module.End.mul_apply]; exact hN _ ih
  have hz : ∀ m : ℕ, ((m.factorial : ℂ))⁻¹ * l ((L ^ m) y) = 0 := fun m => by
    have hm : l ((L ^ m) y) ∈ N.map l := Submodule.mem_map_of_mem (hpow m)
    rw [hl2, Submodule.mem_bot] at hm
    rw [hm, mul_zero]
  have h1 := hU y l
  simp only [hz] at h1
  exact hl1 (h1.unique hasSum_zero)

def pureL {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F]
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' c f := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

end GlobalTheory.SquareAgree.KFinAlg
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LiftRows.Inh
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem goodTypes_of_typesTrue (hL : R.toLevCh.Is A.μ0) (h : GlobalTheory.Mem.Top.TypesTrue D.ntypes R.C.P R.C.W) :
    GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R := by
  intro k
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  refine ⟨_, (h.teich k).symm, h.ser k, fun v j PP hPP a u ha hu => Or.inl ?_⟩
  have hl := h.isCharLab k v j
  have hp := D.host.g_prime k
  have ha0 : (a : Formalism.CyclotomicNorms.Fbar (D.host.g k)) ≠ 0 := by
    rw [ha]; intro h0
    have := (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen_order 1 one_pos
    rw [h0, pow_one] at this
    have h2 := hp.two_le
    have h3 : orderOf (0 : Formalism.CyclotomicNorms.Fbar (D.host.g k)) = 0 := orderOf_eq_zero_iff'.2 fun n hn => by simp [hn.ne']
    omega
  have hcop : a.Coprime (D.host.g k) := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hd
    exact ha0 ((CharP.cast_eq_zero_iff _ (D.host.g k) a).2 hd)
  have han : a ≠ 0 := by rintro rfl; exact ha0 (by simp)
  have h1 := hl.2 (ZMod.unitOfCoprime a hcop) (by rw [ZMod.coe_unitOfCoprime, map_natCast, ha])
  rw [← h1]
  have hE : (a : D.host.E) ≠ 0 := by exact_mod_cast han
  have h2 := (R.C.isMu0 j).atg k PP hPP a hcop (Units.mk0 _ hE) rfl
  have h3 := hL.chi j PP ((hL.Pg PP).2 ⟨k, hPP⟩) (a : 𝓞 D.host.E) (Units.mk0 _ hE) u (by simp) (by rw [hu, map_natCast])
  rw [h2, MonoidHom.inv_apply, _root_.inv_inj] at h3
  rw [h3, MonoidHom.pow_apply]

end GlobalTheory.LiftRows.Inh
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ (q : Place D) (w : WO S T), wAt q w = 0 → VacAt ψ θ S T sS sT ΛS ΛT q f → VacAt ψ θ S T sS sT ΛS ΛT q (heisO ψ S T w f)) ∧ ∀ (p : Place D), IsLocal ψ θ S T sS sT ΛS ΛT p f → (∀ w : WO S T, IsLocal ψ θ S T sS sT ΛS ΛT p (heisO ψ S T (wAt p w) f)) ∧ (∀ (c : ℂ) g, IsLocal ψ θ S T sS sT ΛS ΛT p g → IsLocal ψ θ S T sS sT ΛS ΛT p (c • f + g)) ∧ ∀ τ : D.what₂.Tau, p = .inr τ → ∀ z, IsLocal ψ θ S T sS sT ΛS ΛT p (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
  first | exact @GlobalTheory.PlaceStable.heis_stable | exact GlobalTheory.PlaceStable.heis_stable | (intros; apply GlobalTheory.PlaceStable.heis_stable <;> assumption)
end
