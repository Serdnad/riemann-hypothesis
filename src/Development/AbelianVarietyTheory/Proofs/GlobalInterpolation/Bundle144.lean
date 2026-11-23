module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle098
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle142
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle089
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle137
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemMulLatIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle048
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle099
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousToZModComp
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle133
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle101
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemSuppBarOfNe
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle097
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle111
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle088
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle098
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle100
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelDetCompanion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPadicEmbeddingLeOneOfMemInverseHalfDifferent
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle002
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle728
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle088
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocWDelAtrIff
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

@[expose] public section

section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.ThetaMove

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

theorem moveLaw_at (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word)
    (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.FromHecke W s.σ₀) (hsel : IsSel X sel) (hT : Pr.T u ∈ S) (hg : ∀ k, Pr.g k ∈ S)
    (hs : s.Ok) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hχ : TaylorLogMetric.IsChi D χ)
    (hcop : ∀ P ∈ Sall sel mu u, Nat.Coprime (Ideal.absNorm cc) (Ideal.absNorm P.asIdeal))
    (hEq : B.EqP χ) (hLat : B.LatAll) (hTh : ∀ a b, Even a → Even b → B.ThZeroMem a b)
    (i : ℕ) (hi : i < R.m) (b : ℕ) (hb : b = R.N (i + 1)) (lam' : X.Tau → DomWeight b)
    (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b))
    (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (fr' : Frs X.E b (rowSG Pr sel mu)) (Ξ : HomE X.E (R.N i) b → X.K)
    (h₁ : IsSdLat N₁) (h₂ : IsSdLat N₂) (h₁' : IsSdLat N₁') (h₂' : IsSdLat N₂')
    (ag : AgreeOff (Pr.T u) N₁ N₂) (ag' : AgreeOff (Pr.T u) N₁' N₂')
    (b₁ : InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ N₁' Ξ)
    (b₂ : InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ N₂' Ξ)
    (j₁ : JetsIn (ambOf s B χ cD) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (W.lamTrue u i) (nuLast W u i) N₁ N₁')
    (j₂ : JetsIn (ambOf s B χ cD) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (W.lamTrue u i) (nuLast W u i) N₂ N₂') :
    kerOf (stepT W Ch sel mu cst (ambOf s B χ cD) u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ fr N₁' fr' Ξ =
      moveScal Ch mu u i N₁ N₂ N₁' N₂' •
        kerOf (stepT W Ch sel mu cst (ambOf s B χ cD) u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ fr N₂' fr' Ξ := by
  classical
  have ea : Even (R.N i) := even_N R i
  have eb : Even b := hb ▸ even_N R (i + 1)
  have hA := GlobalTheory.ThetaMove.SeamMoves.moves_ambOf X D s cc δ B χ cD (R.N i) b hX hs hcc hχ hEq hLat
    (hTh _ _ ea eb) ea eb
  have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes X Pr sel S mu u hX hPr hsel hT hg
  have hU : (ambOf s B χ cD).AAUnit (Sall sel mu u) := fun P hP =>
    GlobalTheory.PeriodIdealUnit.locP_AA_eq_one X D s cc δ B χ cD P (bad P hP).2.1 (bad P hP).2.2.1 (hcop P hP)
  set A := ambOf s B χ cD with hAdef
  set Sa := Sall sel mu u with hSa
  have hq : 0 < ∏ P : rowSG Pr sel mu, Formalism.L2.Col.qOf P.1 :=
    Finset.prod_pos fun P _ => Nat.pos_of_ne_zero fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hTpos : 0 < Pr.T u := (hPr.T_prime u).pos
  have hcA : 0 < cAof sel mu cst := pow_pos hq _
  have hcB : 0 < cBof sel mu cst u := Nat.mul_pos hTpos (pow_pos hq _)
  have hoff : ∀ Q : HeightOneSpectrum (𝓞 X.E), Q ∉ Sa → conjPrime₂ Q ∉ Sa → ((Pr.T u : ℕ) : 𝓞 X.E) ∉ Q.asIdeal := by
    intro Q h h' hQ
    rw [← hPr.piT_norm u] at hQ
    rcases Q.isPrime.mem_or_mem hQ with h1 | h1
    · exact h (Finset.mem_union_left _ ((mem_divs (hPr.piT_ne_zero u) Q).2 h1))
    · exact h' (Finset.mem_union_left _ ((mem_divs (hPr.piT_ne_zero u) _).2 ((mem_conjP Q _).2 h1)))
  have hord : ∀ {n : ℕ} {M M' : Submodule (𝓞 X.E) (Sp X.E n)} {P : HeightOneSpectrum (𝓞 X.E)},
      localization₂ P.asIdeal M = localization₂ P.asIdeal M' → ordDet P M = ordDet P M' := fun h => by
    unfold ordDet frameAt
    rw [h]
  let ex : HeightOneSpectrum (𝓞 X.E) → ℤ := fun P =>
    ((b / 2 : ℕ) : ℤ) * idxExp P N₁ N₂ - ((R.N i / 2 : ℕ) : ℤ) * idxExp P N₁' N₂'
  have hTR : (0 : ℝ) < (Pr.T u : ℝ) := by exact_mod_cast hTpos
  have hρ2 : (∏ P ∈ Pr.vT u, (Pr.T u : ℝ) ^ ex P) ^ 2 =
      ∏ P ∈ Sa, ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (volExp P N₂ N₂' - volExp P N₁ N₁') := by
    rw [← Finset.prod_pow, ← Finset.prod_subset (s₁ := Pr.vT u) (s₂ := Sa) Finset.subset_union_left]
    · refine Finset.prod_congr rfl fun P hP => ?_
      rw [hPr.vT_norm u P hP, ← zpow_natCast, ← zpow_mul]
      congr 1
      obtain ⟨a', ha'⟩ := ea
      obtain ⟨b', hb'⟩ := eb
      have e1 : R.N i / 2 = a' := by omega
      have e2 : b / 2 = b' := by omega
      have e3 : (R.N i : ℤ) = 2 * a' := by omega
      have e4 : (b : ℤ) = 2 * b' := by omega
      simp only [ex, volExp, idxExp, e1, e2, e3, e4]
      push_cast
      ring
    · intro P hP hP'
      have h1 : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun h => hP' ((bad P hP).2.2.2.1 h)
      rw [volExp, volExp, hord (ag P h1), hord (ag' P h1), sub_self, zpow_zero]
  have box : ∀ {N : Submodule (𝓞 X.E) (Sp X.E (R.N i))} {N' : Submodule (𝓞 X.E) (Sp X.E b)},
      InBox Sa (cAof sel mu cst) (cBof sel mu cst u) N N' Ξ →
      InBox Sa (cAof sel mu cst) (cBof sel mu cst u) N N' fun x => A.σ₀ (Ξ x) := fun h =>
    ⟨fun x hx => h.1 x fun h0 => hx (by simp [h0]), fun x y hy => by simp only [h.2 x y hy]⟩
  have hcore := core hA (fun P hP => (bad P hP).1) hU h₁ h₂ h₁' h₂' (fun Q h h' => ag Q (hoff Q h h'))
    (fun Q h h' => ag' Q (hoff Q h h')) hcA hcB (box b₁) (box b₂) (Finset.prod_pos fun P _ => zpow_pos hTR _) hρ2
  have full_of_sd : ∀ {n : ℕ} {L : Submodule (𝓞 X.E) (Sp X.E n)}, IsSdLat L → Submodule.IsFullLattice X.E L := by
    intro n L hL
    let := hL.1
    refine { span_eq_top := ?_ }
    let W := Submodule.span X.E (L : Set (Sp X.E n))
    change W = ⊤
    by_contra hW
    let e : Sp X.E n ≃ₗ⋆[X.E] Sp X.E n := starLinearEquiv X.E
    let g : Sp X.E n →ₗ[X.E] Module.Dual X.E W :=
      (LinearMap.domRestrict' W).comp ((hStd X.E n).comp e.toLinearMap)
    have hdim : Module.finrank X.E (Module.Dual X.E W) < Module.finrank X.E (Sp X.E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (a : X.E) : a • e x ∈ L := by
      rw [← hL.2, dualBasic_mem_dual]
      intro y hy
      apply hStd_mem_one_symm
      have hxy : hStd X.E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual X.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
    let i : X.E →ₗ[𝓞 X.E] L :=
      ((LinearMap.toSpanSingleton X.E _ (e x)).restrictScalars (𝓞 X.E)).codRestrict L hsmul
    let : Module.Finite (𝓞 X.E) L := Module.Finite.iff_fg.mpr hL.1.fg
    let : Module.Finite (𝓞 X.E) X.E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective X.E (fun hz => hx₀ (e.map_eq_zero_iff.mp hz)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField X.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 X.E) X.E) (Field.toIsField X.E))
  have f₁ := GlobalTheory.finite_divLat_quot_mulLat_homAt X.E _ _ Sa N₁ N₁' _ _ (full_of_sd h₁) h₁'.1 hcA hcB
  have f₂ := GlobalTheory.finite_divLat_quot_mulLat_homAt X.E _ _ Sa N₂ N₂' _ _ (full_of_sd h₂) h₂'.1 hcA hcB
  have := @Fintype.ofFinite _ f₁
  have := @Fintype.ofFinite _ f₂
  have hj := GlobalTheory.jetOp_identity_of_entire X (R.N i) b A.σ₀ A.cD (W.lamTrue u i) lam' (nuLast W u i) _ _ _ _ _ _ (A.chiF _ _ N₁ N₁')⁻¹ (A.chiF _ _ N₂ N₂')⁻¹
    (∏ P ∈ Pr.vT u, (Pr.T u : X.K) ^ ex P)
    (fun q => analytic_thInd (S := Sa) hA h₁ h₁' (cBof sel mu cst u)
      (Function.surjInv (Submodule.Quotient.mk_surjective _) q : ↥(divLat (cAof sel mu cst) (homAt Sa N₁ N₁'))))
    (fun q => analytic_thInd (S := Sa) hA h₂ h₂' (cBof sel mu cst u)
      (Function.surjInv (Submodule.Quotient.mk_surjective _) q : ↥(divLat (cAof sel mu cst) (homAt Sa N₂ N₂'))))
    (fun q m hm => j₁ _ (Subtype.prop _) m hm) (fun q m hm => j₂ _ (Subtype.prop _) m hm)
    (fun z => by
      have h1 := hcore z
      unfold latSum at h1
      rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype] at h1
      refine h1.trans ?_
      congr 1
      simp)
  have hmU := mUof_conj W Ch sel mu u s.σ₀ hX hPr hCh hsel hT hg i hi
  have m₁ := GlobalTheory.MuOffMove.muOff_move X Pr sel S mu u _ _ N₁ N₂ hX hPr hsel hT hg hmU h₁ h₂ ag
  have m₂ := GlobalTheory.MuOffMove.muOff_move X Pr sel S mu u _ _ N₁' N₂' hX hPr hsel hT hg hmU h₁' h₂' ag'
  unfold stepT
  rw [kerOf_eq, kerOf_eq]
  refine (congrArg _ hj).trans ?_
  rw [smul_smul, smul_smul]
  congr 1
  have hsc : moveScal Ch mu u i N₁ N₂ N₁' N₂' =
      (∏ P ∈ Pr.vT u, ((mUof Ch mu i P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) *
        (∏ P ∈ Pr.vT u, ((mUof Ch mu i P ^ (-idxExp P N₁' N₂') : X.Kˣ) : X.K))⁻¹ * ∏ P ∈ Pr.vT u, (Pr.T u : X.K) ^ ex P := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [locScal, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← zpow_neg, ← zpow_add]
    congr 3
    ring
  rw [hsc, muInvDet, muInvDet, muInvDet, muInvDet, m₁, m₂]
  simp only [mul_inv]
  ring


open GlobalTheory.KerT in
theorem moveStep_of_family : ∀ (Z : Dat) (H : D7) (s : Seam H Z.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ)
    (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ)
    (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu)) (u : Z.Pr.Word) (i : ℕ), i < Z.R.m →
    Hyp Z s cc δ χ cD sel S mu cst u → B.EqP χ → B.LatAll → (∀ a b, Even a → Even b → B.ThZeroMem a b) →
    GlobalTheory.KerT.JetsAll Z.W sel mu cst (ambOf s B χ cD) u i (i + 1) →
    MoveStep Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) := by
  intro Z H s cc δ B χ cD sel S mu cst u i hi h hEq hLat hTh hJ N₁ N₂ N₁' N₂' fr fr' Ξ h₁ h₂ h₁' h₂' ag ag' b₁ b₂
  obtain ⟨hs, hσ, hcc, -, hχ, -⟩ := h.ana
  exact moveLaw_at Z.X Z.Pr Z.R Z.W Z.Ch sel S mu cst u H s cc δ B χ cD h.ok.fields h.ok.primes (hσ ▸ h.ok.hecke) h.isSel h.T_mem
    h.g_mem hs hcc hχ h.cop hEq hLat hTh i hi _ rfl _ N₁ N₂ N₁' N₂' fr fr' Ξ h₁ h₂ h₁' h₂' ag ag' b₁ b₂ (hJ _ _ h₁ h₁') (hJ _ _ h₂ h₂')

end GlobalTheory.ThetaMove
end
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MomT

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable


open Formalism.MainNotions.TaylorLogMetric in
theorem jetMoments_of_unitPeriod
    (hM : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc →
      IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]), p ≠ 2 →
      jacobiSym (-(D.host.d : ℤ)) p = 1 → Nat.Coprime (Ideal.absNorm cc) p →
      ∃ Ω : ℂ_[p], ‖Ω‖ = 1 ∧ GlobalTheory.MomT.MomentsAt D cc δ (B.eNat χ) lam Ω)
    (hE : MovesAll) (hL : LatticeFactsAll) : JetMoments := by
  intro D hD H s cc δ B χ cD ⟨hs, _, hcc, hδ, hχ, hcD⟩ u _ hcop w ι hw
  classical
  obtain ⟨lam, hlam⟩ := (_root_.GlobalTheory.MomPlace.places D.X.K (D.Pr.T u) s.σ₀ ι).1
  obtain ⟨⟨hTs, hTq⟩, -⟩ : (D.Pr.T u ∉ H.host.small ∧ D.Pr.T u ≠ H.host.q) ∧
      ∀ i, D.Pr.g i ∉ H.host.small ∧ D.Pr.g i ≠ H.host.q :=
    ⟨(_root_.GlobalTheory.AAUnitAway.locP_AA_and_primes_ne.2 D H s hD).1 u, (_root_.GlobalTheory.AAUnitAway.locP_AA_and_primes_ne.2 D H s hD).2⟩
  have hT2 : D.Pr.T u ≠ 2 := UpperTheory.Small.ne_two H.host hTs
  have hP := hD.primes
  have hp := hP.T_prime u
  have hn := hP.piT_norm u
  obtain ⟨Ω, hΩ, hmom⟩ := hM H cc δ B χ hcc hδ hχ (D.Pr.T u) lam hT2
    ((_root_.GlobalTheory.MomT.SplitK.splitk H D.X s (D.Pr.piT u) _ hs (hP.piT_Kq u)).2 hp hT2 hn (hP.piT_cop u)) hcop
  obtain ⟨M, _, hMe, hMs⟩ := hcD
  have hcQ : ∀ τ, cD τ ∈ TaylorLogMetric.Qbar := by
    intro τ
    obtain ⟨x, hx, -⟩ := hMs τ
    rw [← hx]
    exact mem_algebraicClosure_iff.2
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (algebraMap M ℂ).toRatAlgHom)
  refine ⟨fun τ => TaylorLogMetric.lamC lam (cD (s.iT τ)) / Ω, fun τ => ?_, ?_⟩
  · obtain ⟨x, hx, hx'⟩ := hMs (s.iT τ)
    rw [norm_div, hΩ, div_one, ← hx]
    exact GlobalTheory.EigenGenerator.norm_generator_eq_one H _ lam hTs hTq M hMe _ x hx'
  intro sel S mu cst hsel hS hcq i b _ hb SG SG' d d' hd hd' Ξ₀ hΞ
  have hev : ∀ j, Even (D.R.N j) := fun j => D.R.k_even.add ((D.R.t_odd.add_one).mul_left j)
  have ha := hev i
  have hb' : Even b := hb ▸ hev _
  obtain ⟨hla, hsm⟩ := hL H D.X s cc δ B χ cD hD.fields hs hcc hδ hχ _ _ ha hb'
  have hπ0 : D.Pr.piT u ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hn
    exact hp.ne_zero (by exact_mod_cast hn.symm)
  have hπ0' : D.X.conjO (D.Pr.piT u) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hn
    exact hp.ne_zero (by exact_mod_cast hn.symm)
  obtain ⟨hfree, hrow⟩ := _root_.GlobalTheory.Proof.AbsNormSplitPlace.main D u sel S mu hD hsel (hS (Or.inr ⟨u, rfl⟩))
    (fun k => hS (Or.inl (by fin_cases k <;> simp)))
  have hUT : ∀ P : HeightOneSpectrum (𝓞 D.X.E), ((D.Pr.T u : ℕ) : 𝓞 D.X.E) ∈ P.asIdeal →
      localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 D.X.E) D.X.E) :=
    fun P h => _root_.GlobalTheory.AAUnitAway.locP_AA_and_primes_ne.1 H D.X s cc δ B χ cD P _ hp hTs hTq h hcop
  have hmemS : ∀ P, P ∈ Sall sel mu u ↔ D.Pr.piT u ∈ P.asIdeal ∨ P ∈ rowSG D.Pr sel mu := by
    intro P
    unfold Sall
    rw [Finset.mem_union, Primes.vT, mem_divs hπ0]
  have hU : (ambOf s B χ cD).AAUnit (Sall sel mu u) := by
    intro P hPS
    rcases (hmemS P).1 hPS with h | h
    · exact hUT P (hn ▸ Ideal.mul_mem_right _ _ h)
    · have bad := _root_.GlobalTheory.ThetaMove.BadPrimes.bad_primes D.X D.Pr sel S mu u hD.fields hP hsel (hS (Or.inr ⟨u, rfl⟩))
        (fun k => hS (Or.inl (by fin_cases k <;> simp))) P hPS
      exact _root_.GlobalTheory.PeriodIdealUnit.locP_AA_eq_one D.X H s cc δ B χ cD P bad.2.1 bad.2.2.1 (hcq P h)
  have hG : Nat.Coprime (∏ P : rowSG D.Pr sel mu, Formalism.L2.Col.qOf P.1) (D.Pr.T u) :=
    Nat.Coprime.prod_left fun P _ => (Nat.coprime_primes (hrow P.1 P.2).1 hp).2 (hrow P.1 P.2).2.1
  have hctx : Ctx (ambOf s B χ cD) (D.R.N i) b (Sall sel mu u) (rowSG D.Pr sel mu) (D.Pr.piT u) (D.Pr.T u)
      ((∏ P : rowSG D.Pr sel mu, Formalism.L2.Col.qOf P.1) ^ cst.B) (cAof sel mu cst) :=
    ⟨hD.fields, ⟨hla.1, hla.2.1, hfree, hU, hla.2.2.2.2⟩,
      fun P h => hUT P (hn ▸ Ideal.mul_mem_left _ _ ((mem_divs hπ0' P).1 h)), hsm, hp, hn, hP.piT_cop u, hmemS,
      fun P h => (hrow P h).2.2.1, hG.pow_left _, hG.pow_left _⟩
  have hN : IsSdLat d.1.N := ⟨d.2.lat, d.2.uni⟩
  have hN' : IsSdLat d'.1.N := ⟨d'.2.lat, d'.2.uni⟩
  obtain ⟨c1, c1'⟩ := _root_.GlobalTheory.MomT.ChiUnit.chi_det_unit H D.X s χ _ lam (D.Pr.piT u) _ d.1.N hD.fields hs hχ hn hN
    fun P h => hd ⟨P, (mem_divs hπ0 P).2 h⟩
  obtain ⟨c2, c2'⟩ := _root_.GlobalTheory.MomT.ChiUnit.chi_det_unit H D.X s χ _ lam (D.Pr.piT u) _ d'.1.N hD.fields hs hχ hn hN'
    fun P h => hd' ⟨P, (mem_divs hπ0 P).2 h⟩
  have hF : (ambOf s B χ cD).chiF (D.R.N i) b d.1.N d'.1.N ∈ TaylorLogMetric.Qbar := mul_mem (zpow_mem c1 _) (zpow_mem c2 _)
  have hF1 : ‖TaylorLogMetric.lamC lam ((ambOf s B χ cD).chiF (D.R.N i) b d.1.N d'.1.N)‖ = 1 := by
    refine (congrArg norm (lamC_mul lam (zpow_mem c1 _) (zpow_mem c2 _))).trans ?_
    rw [lamC_zpow lam c1, lamC_zpow lam c2, norm_mul, norm_zpow, norm_zpow, c1', c2', one_zpow, one_zpow, one_mul]
  refine ⟨fun hseen => ?_, fun hseen => ?_⟩
  · refine type_bar hctx hlam hw d d' hF hF1 Ξ₀ hΞ ?_
    have := _root_.GlobalTheory.MomT.PtMoments.ptMom H D.X s cc δ B χ cD _ lam ι Ω (D.X.conjO (D.Pr.piT u)) (D.R.N i) b hD.fields hs hcc hT2 hcop
      (fun k => (hlam k).2) hcQ (fun τ τ' => ?_) (by rw [conjO_conjO, mul_comm, hn])
      (by rw [conjO_conjO]; exact (hP.piT_cop u).symm) (fun τ => (hw _).1 (hseen τ)) ha hb' hla hsm hmom
    · have e : ((D.X.conjO (D.Pr.piT u) : 𝓞 D.X.E) : D.X.E) = star ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) := rfl
      rwa [e, star_star] at this
    · have e : ((D.X.conjO (D.Pr.piT u) : 𝓞 D.X.E) : D.X.E) = star ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) := rfl
      rw [e, hD.fields.emb_star, hD.fields.emb_star, hP.piT_Kq u τ τ']
  · have hsq : ∀ P ∈ divs (D.Pr.piT u), D.Pr.piT u ∉ P.asIdeal ^ 2 := by
      intro P hPm h2
      refine GlobalTheory.SplitUnram.natCast_notMem_sq D.X.E D.X.conjO (D.Pr.piT u) _ conjO_conjO hp hn (hP.piT_cop u) ?_
        (hP.vT_norm u) P hPm (hn ▸ Ideal.mul_mem_right _ _ h2)
      have h1 : (divs (D.Pr.piT u)).card = Module.finrank ℚ D.X.F := (hP.vT_card u).trans hD.fields.card_Tau
      rw [h1, ← Module.finrank_mul_finrank ℚ D.X.F D.X.E, hD.fields.rankE, mul_comm]
    obtain ⟨N'', hN'', hc⟩ := _root_.GlobalTheory.MomT.MomentCompanion.companion D.X b SG' (D.Pr.piT u) d' hD.fields hπ0 (hP.piT_cop u) hsq
    have hval := _root_.GlobalTheory.MomT.ChiMove.chi_move H D.X s χ b SG' (D.Pr.piT u) d' N'' hD.fields hs hχ hπ0 (hP.piT_cop u) hsq hN'' hc
    set k : D.X.K := ∏ τ, (D.X.emb τ (((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) / star ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E)))⁻¹ with hk
    have hval' : χ (TaylorLogMetric.detId H (s.lat d'.1.N) (s.lat N'')) = s.σ₀ k := by
      rw [hval, hk, map_prod]
      exact Finset.prod_congr rfl fun τ _ => (map_inv₀ _ _).symm
    have hk0 : k ≠ 0 := by
      have h0 : ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) ≠ 0 := by exact_mod_cast hπ0
      exact Finset.prod_ne_zero_iff.2 fun τ _ => inv_ne_zero ((map_ne_zero _).2 (div_ne_zero h0 (star_ne_zero.2 h0)))
    have hkn : ‖ι k‖ ≤ (D.Pr.T u : ℝ) ^ D.X.f := by
      rw [hk, map_prod, norm_prod]
      refine (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun τ _ => ?_).trans_eq
        (Finset.prod_const (D.Pr.T u : ℝ))
      rw [map_inv₀]
      exact norm_ratio_le (ι.comp (D.X.emb τ)) hn
    have hcard : (divs (D.Pr.piT u)).card = D.X.f := hP.vT_card u
    have key := type_p hctx hlam hw d d' hd hF hF1 Ξ₀ hΞ
      (_root_.GlobalTheory.MomT.PtMoments.ptMom H D.X s cc δ B χ cD _ lam ι Ω (D.Pr.piT u) (D.R.N i) b hD.fields hs hcc hT2 hcop
        (fun k => (hlam k).2) hcQ (hP.piT_Kq u) hn (hP.piT_cop u) (fun τ => (hw _).1 (hseen τ)) ha hb' hla hsm hmom)
      (hP.vT_norm u) N'' hN'' hc (s.σ₀ (k ^ (D.R.N i / 2))) (hlam _).1 ?_ ?_
    · rw [hcard] at key
      exact key
    · rw [(hlam _).2, map_pow, norm_pow, ← pow_mul, Nat.div_two_mul_two_of_even ha, hcard, pow_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) hkn _
    · intro R hR z
      have hmv := _root_.GlobalTheory.MomT.Move.move H D.X s cc δ B χ cD _ b d.1.N d'.1.N N'' hD.fields hs (hE H cc δ B χ hcc hδ hχ) ha hb' hla
        hN hN' hN'' R hR z
      have hR0 : ((Real.sqrt (R.card : ℝ) : ℝ) : ℂ) ≠ 0 := by
        obtain ⟨x, hx, -⟩ := hR.2.2 0 (zero_mem _)
        have : (0 : ℝ) < R.card := by exact_mod_cast Finset.card_pos.2 ⟨x, hx⟩
        exact_mod_cast (Real.sqrt_pos.2 this).ne'
      have hσ : s.σ₀ k ≠ 0 := (map_ne_zero _).2 hk0
      rw [hmv, hval', map_pow, zpow_neg, zpow_natCast]
      field_simp

end GlobalTheory.MomT
end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

noncomputable section

open Formalism.UG

namespace GlobalTheory.InfUCompact

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem compactSpace_UJ (E : Type) [Field E] (n : ℕ) :
    CompactSpace (UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E))) := by
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) (Cinf E)) := GlobalTheory.KinfCompactness.compactSpace_Kinf E n
  let f : Matrix.unitaryGroup (Fin n) (Cinf E) → GL (Fin n) (Cinf E) := fun u =>
    ⟨u.1, star u.1, Matrix.mem_unitaryGroup_iff.1 u.2, Matrix.mem_unitaryGroup_iff'.1 u.2⟩
  have hf : Continuous f :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩
  have hr : Set.range f =
      (UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E)) : Set (GL (Fin n) (Cinf E))) := by
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      change cT (starRingEnd (Cinf E)) u.1 * 1 * u.1 = 1
      rw [mul_one]
      exact Matrix.mem_unitaryGroup_iff'.1 u.2
    · intro hg
      have h : cT (starRingEnd (Cinf E)) (g : Matrix (Fin n) (Fin n) (Cinf E)) * 1 * g = 1 := hg
      rw [mul_one] at h
      exact ⟨⟨g.1, Matrix.mem_unitaryGroup_iff'.2 h⟩, Units.ext rfl⟩
  exact isCompact_iff_compactSpace.1 (hr ▸ isCompact_range hf)

theorem range_infPt : Set.range (GlobalTheory.DefiniteDense.infPt (E := E) (n := n)) = (infU E n : Set (UA E n)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact pFin_infGL _
  · intro hx
    have hp : ∀ a : Ad E, pInf E (conjAd E a) = starRingEnd (Cinf E) (pInf E a) :=
      fun a => (infEq E).symm_apply_apply _
    have hM : GeneralLinearGroup.map (pInf E) x.1 ∈
        UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E)) := by
      have h0 : cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * x.1 = 1 := x.2
      rw [mul_one] at h0
      have e : cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) =
          (cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E))).map (pInf E) := by
        ext i j
        simp [Formalism.UG.cT, hp]
      change cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) * 1 *
        (x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E) = 1
      rw [e, mul_one, ← Matrix.map_mul, h0, Matrix.map_one _ (map_zero _) (map_one _)]
    refine ⟨⟨_, hM⟩, Subtype.ext (ga_ext ?_ ?_)⟩
    · exact pInf_infGL _
    · exact (pFin_infGL _).trans (Eq.symm hx)

theorem compactSpace_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
    CompactSpace (infU E n) := by
  intro E _ _ _ n
  haveI := compactSpace_UJ E n
  have h : IsCompact (infU E n : Set (UA E n)) :=
    range_infPt (E := E) (n := n) ▸ isCompact_range GlobalTheory.DefiniteDense.continuous_infPt
  exact isCompact_iff_compactSpace.1 h

end GlobalTheory.InfUCompact
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem _root_.GlobalTheory.T.mem_locW_delAtr_iff' : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K)), (∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) → ∀ {n : ℕ} (lam lam' : ι → DomWeight n), (∀ τ, (lam τ).natW = (lam' τ).natW) → ∀ (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E M → ∀ (w : Pl.Pl) (B : GL (Fin n) E), IsLocBasis (Pl.resChar w) (M : Set (Fin n → E)) B → ∀ F : Formalism.L2.DIV.VV K lam, F ∈ locW Pl w (delAtr emb lam M) ↔ MvPolynomial.map σ (rhoVr emb lam B⁻¹ F).1 ∈ vlIntSpan σ Pl w lam' := by
  first | exact @GlobalTheory.WeylLocOnePlace.mem_locW_delAtr_iff | exact GlobalTheory.WeylLocOnePlace.mem_locW_delAtr_iff | (intros; apply GlobalTheory.WeylLocOnePlace.mem_locW_delAtr_iff <;> assumption)
end
