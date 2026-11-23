module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightLawGoodOfFieldEmbedding
import Formalism.LocalRingCardinality.Lemmas
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle012
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetCConstMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1058
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle294
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Core.ColNorm

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.StepZero

section Forget

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
  {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
  (pref : DecoF X.E n ST SG Q → Prop) (lam : X.Tau → DomWeight n) {Λ₀ : LevFam X.E X.K n SG}
  (pf : ∀ b, (stepY ST y β Λ Θ pref).D b → Prop)

def secR [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    (base ST lam Λ₀).Sec where
  rep c := (((stepY ST y β Λ Θ pref).reRep pf).rep ((clEquiv pref lam hy hΛ hΘ).symm c)).1.1.deco
  spec c := by
    obtain ⟨⟨b, q⟩, rfl⟩ := (clEquiv pref lam hy hΛ hΘ).surjective c
    rw [Equiv.symm_apply_apply]
    refine (clMap_cl (Θ := Θ) pref lam hΛ b _).symm.trans ?_
    exact congrArg (fun q => clMap (y := y) (Λ := Λ) (Θ := Θ) (Λ₀ := Λ₀) pref lam ⟨b, q⟩) (((stepY ST y β Λ Θ pref).reRep pf).rp_spec b q)

theorem majAt_eq_ipAt [Unique β] (hX : X.Ok) (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (hS : ((stepY ST y β Λ Θ pref).reRep pf).Ok)
    (h : (((stepY ST y β Λ Θ pref).reRep pf).fam X.emb lam).Ok) (h₀ : (base ST lam Λ₀).Ok) (hr : (base ST lam Λ₀).Rat)
    (v : InfinitePlace X.K) (x : ((stepY ST y β Λ Θ pref).reRep pf).FormsK X.emb lam h) (φ : (base ST lam Λ₀).EqFun)
    (hx : ∀ c, x.1 c = φ.1 (((stepY ST y β Λ Θ pref).reRep pf).rep c).1.1.deco) :
    Formalism.HermitianLatticesTheory.majAt (((stepY ST y β Λ Θ pref).reRep pf).hlat X.emb lam h).b
      (((stepY ST y β Λ Θ pref).reRep pf).hlat X.emb lam h).X v x x = (base ST lam Λ₀).ipAt h₀ v φ φ := by
  obtain ⟨σ, hσ⟩ := hX.conjK
  have hF : FOk X.emb σ := ⟨hX.conjE, hX.emb_star, hσ⟩
  refine (majAt_eq_classSum (((stepY ST y β Λ Θ pref).reRep pf).csd X.emb lam h) (GlobalTheory.Mem.LatGood.hasRatBasis _ _ σ lam hF hS h)
    (fun v => GlobalTheory.Mem.LatGood.step_gram_posDef _ _ σ lam hF hS h v.embedding) v _ _).trans ?_
  rw [hr.ipAt_indep h₀ (secR pref lam pf hy hΛ hΘ)]
  refine (@Fintype.sum_equiv _ _ _ (_) (_) _ (clEquiv pref lam hy hΛ hΘ).symm _ _ fun c => ?_).symm
  rw [hx]
  congr 3
  refine (card_stab pref hy hΛ hΘ ((clEquiv pref lam hy hΛ hΘ).symm c).1 (((stepY ST y β Λ Θ pref).reRep pf).rep ((clEquiv pref lam hy hΛ hΘ).symm c))).symm.trans ?_
  exact @Nat.card_eq_fintype_card _ (_)

end Forget

end GlobalTheory.Core.ColNorm

namespace GlobalTheory.Core.ColNorm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem nrm_stepZero_eq : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (x : ((I.fm l u a).lat 0).V) (φ : ColsK I u), IsCol I u a l x φ → ∀ v, nrm ((I.fm l u a).lat 0) v x = nrm (Mu0H (Pr := B.primes X) B.wts I.Ch hX u) v φ := by
  intro B X I h hX l u a x φ hc v
  have hL := h.idx_ok a
  letI := StepZero.idxUnique hL
  have key := majAt_eq_ipAt ((I.Tp a).pref u 0) (lamT (B.hcW u) 0) (I.pref u a 0) hX
    (StepZero.ysAt_zero I.sel (I.tup a) (I.cst a)) (StepZero.levGAt_zero (I.Tp a) hL) (StepZero.levQAt_zero (I.Tp a) hL)
    ((l.ch u a).step 0) ((l.fmL u a).fam 0) (colOk (Pr := B.primes X) B.wts I.Ch hX u 0) (colRat (Pr := B.primes X) B.wts I.Ch hX u 0) v x φ hc
  have key2 := key.trans (latH_maj (Pr := B.primes X) B.wts I.Ch hX u 0 v φ φ).symm
  have h1 := normAt_sq_eq_majAt ((I.fm l u a).lat 0).b ((I.fm l u a).lat 0).X v x
  have h2 := normAt_sq_eq_majAt (Mu0H (Pr := B.primes X) B.wts I.Ch hX u).b (Mu0H (Pr := B.primes X) B.wts I.Ch hX u).X v φ
  exact (pow_left_inj₀ (normAt_nonneg _ _ _ _) (normAt_nonneg _ _ _ _) two_ne_zero).1
    (h1.trans ((congrArg Complex.re key2).trans h2.symm))

end GlobalTheory.Core.ColNorm

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.Core.Ht2.KernelS

theorem kernel_le_sharp (hB : GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.BlockBound) (hT : FamilyTie) (hV : FamilyVectors) (hL : PeriodLattices)
    (hR : CosetRefinement) (hP : GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod) (C : ℕ) : ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ B : Base D D.host.ccK dl,
      FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → ∀ i j, j = i + 1 → i < N.R.m →
      ∀ (L : Submodule (𝓞 X.E) (Sp X.E (N.R.N i))) (fr : Frs X.E (N.R.N i) (rowSG Pr sel mu))
        (L' : Submodule (𝓞 X.E) (Sp X.E (N.R.N j))) (fr' : Frs X.E (N.R.N j) (rowSG Pr sel mu)), IsSdLat L → IsSdLat L' →
      ∀ Ξ : HomE X.E (N.R.N i) (N.R.N j) → X.K, SmallDatum (Sall sel mu u) L L' (Pr.T u * (Pr.g 0 * Pr.g 1)) Ξ
        (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2)) →
      ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (hM : ThetaFieldData B cD s.σ₀ N.R M) (ρ : M →ₐ[ℚ] ℂ),
        CoefOpLe ((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1)) (W.lamTrue u i) (W.lamTrue u j)
          (kerOf (stepC W Ch sel mu cst (ambOf s B χ cD) u i (W.lamTrue u j)) (Sall sel mu u) (cAof sel mu cst)
            (cBof sel mu cst u) L fr L' fr' Ξ)
          (Real.exp (kernelBound_sq N δ (Pr.T u) CK j (fun z => logOmAt B cD M ρ (s.iT (pl z)))
            (logThAt B M ρ (N.R.N (j - 1)) (N.R.N j)) 1 1 1 1)) := by
  obtain ⟨CK, hCK, hnum⟩ := GlobalTheory.T.exists_jetBlockBound_le_exp_kernelBound C
  refine ⟨CK, hCK, ?_⟩
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H B hFD i j hj hi L fr L' fr' hL1 hL2 Ξ hΞ M _ hM ρ
  subst hj
  have H' := H
  obtain ⟨hHost, hWt, hCh, hAn, hmu, hsh, hI, hSz, hRows⟩ := H'
  obtain ⟨trd, -, -, -, tf, -, tE, -, tcc⟩ := GlobalTheory.T.numDatum_numbers_eq_host_of_compatible D N X s Pr hHost
  obtain ⟨-, -, -, -, hpsi, hadm, hX, hs, -, hPr, -, -, hg, -⟩ := hHost
  obtain ⟨-, -, -, hprod, hTodd, hgodd, hS⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  obtain ⟨hstep, hnu⟩ := GlobalTheory.Core.Ht2.StepRowsS.weights_rows CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi
  have hcrv : StandardLatticesGL3.Crv D D.host.ccK dl := ⟨tcc, hAn.1⟩
  have hY := GlobalTheory.T.kernelConstant_exponents_finite D B.γ₀ B.kc
  have hev : ∀ l, Even (N.R.N l) := fun l => by
    unfold Ranks.N
    exact N.R.k_even.add ((N.R.t_odd.add_one).mul_left l)
  have hlt : N.R.N i < N.R.N (i + 1) := by
    unfold Ranks.N
    nlinarith
  obtain ⟨hAdm, hbase⟩ := GlobalTheory.T.normalisedFamily_standardLattices_eq_baseVector D _ dl B χ hAn.2.1 (hV D _ dl B χ hadm hpsi tcc hAn.1 hAn.2.1 hY) _ _ (hev i) (hev (i + 1))
  have hE0 := hT D _ dl B χ hadm hpsi tcc hAn.1 hAn.2.1 hY _ B.t0 _ _ _ _ hAdm
  rw [hbase] at hE0
  have hgpos : 0 < Pr.g 0 * Pr.g 1 := Nat.mul_pos (hPr.g_prime 0).pos (hPr.g_prime 1).pos
  have hfpos : 0 < N.R.f := by
    unfold Ranks.f Ranks.n
    have := N.R.ord_pos
    omega
  have hBpos := hI.cst_ok.B_pos
  have hcA : cAof sel mu cst = (Pr.g 0 * Pr.g 1) ^ (N.R.f * cst.A) := by unfold cAof; rw [hprod, pow_mul]
  have hcB : cBof sel mu cst u = Pr.T u * (Pr.g 0 * Pr.g 1) * (Pr.g 0 * Pr.g 1) ^ (N.R.f * cst.B - 1) := by
    unfold cBof
    have h1 : N.R.f * cst.B = (N.R.f * cst.B - 1) + 1 := by
      have := Nat.mul_pos hfpos hBpos
      omega
    rw [hprod, ← pow_mul]
    conv_lhs => rw [h1]
    ring
  have hodd : Odd (cAof sel mu cst * cBof sel mu cst u) := by
    have h1 : Odd (Pr.g 0 * Pr.g 1) := (hgodd 0).mul (hgodd 1)
    rw [hcA, hcB]
    exact h1.pow.mul ((hTodd.mul h1).mul h1.pow)
  have hInd := hR X (ambOf s B χ cD) _ _ (Sall sel mu u) _ hX.ok (fun P hP => (hS P hP).2) hodd
    (hL D X s _ dl B χ cD hX.ok hs hadm hpsi tcc hAn.1 hAn.2.1 hAn.2.2 hY _ _ (Sall sel mu u) (hev i) (hev (i + 1))
      (fun P hP => (hS P hP).1) (GlobalTheory.T.periodLatticeIdeal_trivial_at_badPrimes CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H B))
  have hJ := hFD i hi
  have hc0 : ∀ τ, cD τ ≠ 0 := (GlobalTheory.T.mean_logMetric_generator_eq_meanPeriod D _ dl cD hcrv (hP D _ dl tcc hAn.1) hAn.2.2).1
  have hsc : ‖((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1))
      (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) L fr *
        (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) L' fr')⁻¹)‖ ≤ 1 := by
    rw [map_mul, map_inv₀, norm_mul, norm_inv]
    rcases GlobalTheory.ScalarModulusS.norm_muInvDet_zero_or_one CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi _ L fr
      ((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1)) with h1 | h1 <;>
    rcases GlobalTheory.ScalarModulusS.norm_muInvDet_zero_or_one CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi _ L' fr'
      ((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1)) with h2 | h2 <;> rw [h1, h2] <;> norm_num
  unfold stepC
  rw [hcB] at hInd hJ ⊢
  have key := block hB D X s _ dl B χ cD _ hX.ok hs hcrv B.t0 hc0 _ _ hlt ((hev i).mul_right _) hE0
    (W.lamTrue u i) (W.nuW u (i + 1)) (W.lamTrue u (i + 1)) hstep (Sall sel mu u) (rowSG Pr sel mu) (cAof sel mu cst)
    (Pr.T u * (Pr.g 0 * Pr.g 1)) ((Pr.g 0 * Pr.g 1) ^ (N.R.f * cst.B - 1)) (by rw [hcA]; positivity)
    (Nat.mul_pos (hPr.T_prime u).pos hgpos) (by positivity) hInd hJ sel (mUof Ch mu i) (muAt Ch sel mu cst i) L fr L' fr' hL1 hL2
    Ξ _ hΞ M hM.1 ρ hM.2.1 hM.2.2.1 (hM.2.2.2 i hi) hsc
  have hn := hnum N δ (Pr.T u) i X.Tau pl (W.nuW u (i + 1)) (fun z => logOmAt B cD M ρ (s.iT (pl z)))
    (logThAt B M ρ (N.R.N i) (N.R.N (i + 1))) hi (hPr.T_prime u).two_le (fun τ => (hstep τ).1) hnu
  intro x
  refine (key x).trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · refine le_trans (le_of_eq ?_) hn
    simp only [supConst, tf, tE, ← trd, hg, Equiv.apply_symm_apply]
  · exact sqAt_nonneg _ _ _

end GlobalTheory.Core.Ht2.KernelS
end
end

section

noncomputable section

namespace GlobalTheory.CuspGeo.MeanValue

section Abstract

open GlobalTheory.SmoothForms

variable {L G ι : Type} [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] [Fintype ι]

theorem norm_sub_le (e : L → G) (he0 : e 0 = 1) (he : ∀ (Z : L) (s t : ℝ), e ((s + t) • Z) = e (s • Z) * e (t • Z))
    (b : Module.Basis ι ℝ L) {φ : G → ℂ} (hφ : Sm e φ) (g : G) (Z : L) (a : ℝ) (ha : ∀ i, |b.repr Z i| ≤ a) (c : ι → ℝ)
    (hc : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Der e (b i) φ (g * e (t • Z))‖ ≤ c i) :
    ‖φ (g * e Z) - φ g‖ ≤ a * ∑ i, c i := by
  have hc0 : ∀ i, 0 ≤ c i := fun i => (norm_nonneg _).trans (hc i 0 ⟨le_refl 0, zero_le_one⟩)

  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => φ (g * e (s • Z)))
      (fderiv ℝ (fun X : L => φ (g * e (t • Z) * e X)) ((t - t) • Z) Z) t := by
    intro t
    have hF : Differentiable ℝ (fun X : L => φ (g * e (t • Z) * e X)) :=
      (hφ (g * e (t • Z))).differentiable (by simp)
    have h1 : HasDerivAt (fun s : ℝ => (s - t) • Z) ((1 : ℝ) • Z) t :=
      ((hasDerivAt_id' t).sub_const t).smul_const Z
    rw [one_smul] at h1
    have h2 := (hF ((t - t) • Z)).hasFDerivAt.comp_hasDerivAt t h1
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show φ (g * e (s • Z)) = φ (g * e (t • Z) * e ((s - t) • Z))
    rw [mul_assoc, ← he, show t + (s - t) = s by ring]

  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fun X : L => φ (g * e (t • Z) * e X)) 0 Z‖ ≤ a * ∑ i, c i := by
    intro t ht
    set F' := fderiv ℝ (fun X : L => φ (g * e (t • Z) * e X)) 0 with hF'
    have hZ : F' Z = ∑ i, b.repr Z i • F' (b i) := by
      have : F' Z = F' (∑ i, b.repr Z i • b i) := by rw [b.sum_repr]

      rw [this, map_sum]
      simp only [map_smul]
    rw [hZ, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    have hi : ‖F' (b i)‖ ≤ c i := by
      have := hc i t ht
      rwa [DerLinear.der_eq_fderiv hφ] at this
    exact mul_le_mul (ha i) hi (norm_nonneg _) ((abs_nonneg _).trans (ha i))
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => φ (g * e (s • Z))) (fun t _ => (hderiv t).hasDerivWithinAt)
    (fun t ht => by
      rw [sub_self, zero_smul]
      exact key t (Set.Ico_subset_Icc_self ht))
  simpa [he0] using hmv

theorem exists_coord_bound (b : Module.Basis ι ℝ L) : ∃ K : ℝ, 0 ≤ K ∧ ∀ Z i, |b.repr Z i| ≤ K * ‖Z‖ := by
  have : FiniteDimensional ℝ L := Module.Finite.of_basis b
  let f : ι → L →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  refine ⟨∑ i, ‖f i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun Z i => ?_⟩
  have h1 : |b.repr Z i| = ‖f i Z‖ := by
    simp [f, Real.norm_eq_abs]
  rw [h1]
  exact ((f i).le_opNorm Z).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => norm_nonneg (f j)) (Finset.mem_univ i)) (norm_nonneg Z))

end Abstract

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem expInf_zero (R : RealPoints θ V) : expInf θ V 0 = 1 := by
  have hE := isExpFam_expInf R
  refine R.2.2.1 _ (hE (0 : LieN V)).1 _ (GinfC V).one_mem fun τ => ?_
  rw [(hE (0 : LieN V)).2 τ, R.2.2.2.2.1 1 (GfC V).one_mem τ]
  show NormedSpace.exp (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ) = 1
  exact NormedSpace.exp_zero

theorem expInf_add (R : RealPoints θ V) (Z : LieN V) (s t : ℝ) :
    expInf θ V ((s + t) • Z) = expInf θ V (s • Z) * expInf θ V (t • Z) := by
  have hE := isExpFam_expInf R
  refine R.2.2.1 _ (hE ((s + t) • Z)).1 _ (mul_mem (hE (s • Z)).1 (hE (t • Z)).1) fun τ => ?_
  rw [R.2.2.2.1, (hE ((s + t) • Z)).2 τ, (hE (s • Z)).2 τ, (hE (t • Z)).2 τ]
  show NormedSpace.exp ((s + t) • (Z τ).1) = NormedSpace.exp (s • (Z τ).1) * NormedSpace.exp (t • (Z τ).1)
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl (Z τ).1).smul_right t).smul_left s)

theorem continuous_expInf (hθ : IsInfFam θ) (R : RealPoints θ V) : Continuous (expInf θ V) := by
  have H := isLieData R
  have h1 : Continuous fun X : LieN V => NormedSpace.exp (jInf V X) :=
    (DerLinear.contDiff_exp H).continuous
  exact (GlobalTheory.Mem.DerClosed.continuousOn_secInf hθ V).comp_continuous h1 fun X => DerLinear.exp_unitary H X


open Classical in
theorem exists_basis (V : HSp D) : ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ (LieN V)) (p : ι → D.what₂.Tau)
    (X : ∀ i, LieAt V (p i)), ∀ i, b i = atPlace V (p i) (X i) := by
  refine ⟨Σ τ, Fin (Module.finrank ℝ (lieU (gramAt D V τ)).toSubmodule), inferInstance,
    Pi.basis fun τ => Module.finBasis ℝ (lieU (gramAt D V τ)).toSubmodule, fun i => i.1,
    fun i => ⟨(Module.finBasis ℝ (lieU (gramAt D V i.1)).toSubmodule i.2).1,
      (Module.finBasis ℝ (lieU (gramAt D V i.1)).toSubmodule i.2).2⟩, fun i => ?_⟩
  exact (Pi.basis_apply _ i).trans rfl

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem norm_lieN_le (Z : LieN V) {r : ℝ} (hr : 0 ≤ r) (h : ∀ τ i j, ‖(Z τ).1 i j‖ ≤ r) : ‖Z‖ ≤ r := by
  refine (pi_norm_le_iff_of_nonneg hr).2 fun τ => ?_
  rw [Submodule.coe_norm]
  exact (Matrix.norm_le_iff hr).2 (h τ)

end

theorem exists_log (hθ : IsInfFam θ) (R : RealPoints θ V) : ∃ δ₁ C : ℝ, 0 < δ₁ ∧ 0 ≤ C ∧
    ∀ (u : GA D V) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → CloseR θ V u δ → ∃ Z : LieN V, expInf θ V Z = u ∧ ‖Z‖ ≤ C * δ := by
  have hG : ∀ τ, IsUnit (gramAt D V τ).det := fun τ => (R.1 τ).2
  choose δτ Cτ hδτ hτ using fun τ => GlobalTheory.T.exists_log_near_one_unitaryGroup_of_form_linear_bound V.rank (gramAt D V τ) (hG τ)
  obtain ⟨δ₁, hδ₁, hle⟩ : ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ τ, δ₁ ≤ δτ τ := by
    rcases isEmpty_or_nonempty D.what₂.Tau with h | h
    · exact ⟨1, one_pos, fun τ => (IsEmpty.false τ).elim⟩
    · obtain ⟨τ₀, hτ₀⟩ := Finite.exists_min δτ
      exact ⟨δτ τ₀, hδτ τ₀, hτ₀⟩
  have hC : ∀ τ, Cτ τ ≤ ∑ τ', |Cτ τ'| := fun τ =>
    (le_abs_self _).trans (Finset.single_le_sum (fun τ' _ => abs_nonneg (Cτ τ')) (Finset.mem_univ τ))
  refine ⟨δ₁, ∑ τ, |Cτ τ|, hδ₁, Finset.sum_nonneg fun τ _ => abs_nonneg _, fun u δ hδ hδle hu => ?_⟩

  have hX : ∀ τ, ∃ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 ∧
      NormedSpace.exp X = infMat D.sp.cm.sig V.gram (θ τ) u ∧ ∀ i j, ‖X i j‖ ≤ Cτ τ * δ := fun τ =>
    hτ τ _ δ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V u τ) (hδle.trans (hle τ)) (hu.2 τ)
  choose X hXl hXe hXn using hX
  let Z : LieN V := fun τ => ⟨X τ, (mem_lieAt_iff τ (X τ)).1 (hXl τ)⟩
  refine ⟨Z, ?_, ?_⟩
  · have hE := isExpFam_expInf R
    refine R.2.2.1 _ (hE Z).1 _ hu.1 fun τ => ?_
    rw [(hE Z).2 τ]
    exact hXe τ
  · refine norm_lieN_le Z (mul_nonneg (Finset.sum_nonneg fun τ _ => abs_nonneg _) hδ) fun τ i j => ?_
    exact (hXn τ i j).trans (mul_le_mul_of_nonneg_right (hC τ) hδ)

theorem mean_value : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ V : HSp D, ∃ (B : Finset (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (Ω : Set (GA D V)) (C δ₁ : ℝ), (∀ p ∈ B, p.2 ∈ lieAt V p.1) ∧ IsCompact Ω ∧ 0 < δ₁ ∧ 0 ≤ C ∧ ∀ ψ : GA D V → ℂ, SmoothW θ V ψ → ∀ (g u : GA D V) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → CloseR θ V u δ → ∀ c : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ → ℝ, (∀ p ∈ B, ∀ w ∈ Ω, ‖Rder θ V p.1 p.2 ψ (g * w)‖ ≤ c p) → ‖ψ (g * u) - ψ g‖ ≤ C * δ * ∑ p ∈ B, c p := by
  intro D θ hθ V
  classical
  have R : RealPoints θ V := (RealPts.realPoints D).2 θ hθ V
  obtain ⟨ι, hι, b, p, X, hb⟩ := exists_basis V
  obtain ⟨K, hK, hKb⟩ := exists_coord_bound b
  obtain ⟨δ₁, C₀, hδ₁, hC₀, hlog⟩ := exists_log hθ R
  have : FiniteDimensional ℝ (LieN V) := Module.Finite.of_basis b
  set B := Finset.univ.image fun i => (p i, (X i).1) with hB
  have hmemB : ∀ i, (p i, (X i).1) ∈ B := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have h0 : expInf θ V 0 ∈ expInf θ V '' Metric.closedBall 0 (C₀ * δ₁) :=
    ⟨0, Metric.mem_closedBall_self (mul_nonneg hC₀ hδ₁.le), rfl⟩
  refine ⟨B, expInf θ V '' Metric.closedBall 0 (C₀ * δ₁), K * C₀ * Fintype.card ι, δ₁, ?_, ?_, hδ₁,
    mul_nonneg (mul_nonneg hK hC₀) (Nat.cast_nonneg _), ?_⟩
  · intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hq
    exact (mem_lieAt_iff _ _).2 (X i).2
  · exact (isCompact_closedBall 0 _).image (continuous_expInf hθ R)
  · intro ψ hψ g u δ hδ hδle hu c hc
    obtain ⟨Z, rfl, hZ⟩ := hlog u δ hδ hδle hu
    have hsm : Sm (expInf θ V) ψ := (isSmoothInf_iff ψ).1 ((smooth_iff R ψ).1 hψ)
    have hcn : ∀ q ∈ B, 0 ≤ c q := fun q hq => (norm_nonneg _).trans (hc q hq _ h0)
    have ha : ∀ i, |b.repr Z i| ≤ K * (C₀ * δ) := fun i =>
      (hKb Z i).trans (mul_le_mul_of_nonneg_left hZ hK)
    have hder : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖Der (expInf θ V) (b i) ψ (g * expInf θ V (t • Z))‖ ≤ c (p i, (X i).1) := by
      intro i t ht
      rw [hb i, ← lieDer_eq, ← Rder_eq R]
      refine hc _ (hmemB i) _ ⟨t • Z, ?_, rfl⟩
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖Z‖ ≤ 1 * (C₀ * δ) := mul_le_mul ht.2 hZ (norm_nonneg _) zero_le_one
        _ ≤ C₀ * δ₁ := by rw [one_mul]; exact mul_le_mul_of_nonneg_left hδle hC₀
    have key := norm_sub_le (expInf θ V) (expInf_zero R) (expInf_add R) b hsm g Z (K * (C₀ * δ)) ha
      (fun i => c (p i, (X i).1)) hder
    have hsum : ∑ i, c (p i, (X i).1) ≤ Fintype.card ι * ∑ q ∈ B, c q := by
      calc ∑ i, c (p i, (X i).1) ≤ ∑ _i : ι, ∑ q ∈ B, c q :=
            Finset.sum_le_sum fun i _ => Finset.single_le_sum hcn (hmemB i)
        _ = Fintype.card ι * ∑ q ∈ B, c q := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc ‖ψ (g * expInf θ V Z) - ψ g‖ ≤ K * (C₀ * δ) * ∑ i, c (p i, (X i).1) := key
      _ ≤ K * (C₀ * δ) * (Fintype.card ι * ∑ q ∈ B, c q) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg hK (mul_nonneg hC₀ hδ))
      _ = K * C₀ * Fintype.card ι * δ * ∑ q ∈ B, c q := by ring

end GlobalTheory.CuspGeo.MeanValue

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.CocompactParam

theorem eventually_close {G P : Type*} [TopologicalSpace G] [TopologicalSpace P] (K : G → P → ℂ)
    (hK : Continuous (Function.uncurry K)) {C : Set G} (hC : IsCompact C) (p₀ : P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p in nhds p₀, ∀ g ∈ C, ‖K g p - K g p₀‖ < ε := by
  refine hC.eventually_forall_of_forall_eventually (P := fun p g => ‖K g p - K g p₀‖ < ε) fun g _ => ?_
  have h1 : Continuous fun z : P × G => K z.2 z.1 := hK.comp (continuous_snd.prodMk continuous_fst)
  have h2 : Continuous fun z : P × G => K z.2 p₀ := hK.comp (continuous_snd.prodMk continuous_const)
  have hc : Continuous fun z : P × G => ‖K z.2 z.1 - K z.2 p₀‖ := (h1.sub h2).norm
  exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using hε)

theorem continuous_setIntegral_of_unif {G P : Type*} [MeasurableSpace G] [TopologicalSpace P] (μ : Measure G)
    (𝓕 : Set G) (hfin : μ 𝓕 < ⊤) (K : G → P → ℂ) (hint : ∀ p, IntegrableOn (fun g => K g p) 𝓕 μ)
    (hcl : ∀ p₀, ∀ ε : ℝ, 0 < ε → ∀ᶠ p in nhds p₀, ∀ g, ‖K g p - K g p₀‖ < ε) :
    Continuous fun p => ∫ g in 𝓕, K g p ∂μ := by
  refine continuous_iff_continuousAt.2 fun p₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hm : 0 ≤ μ.real 𝓕 := measureReal_nonneg
  have hδ : 0 < ε / (μ.real 𝓕 + 1) := by positivity
  filter_upwards [hcl p₀ _ hδ] with p hp
  rw [dist_eq_norm, ← integral_sub (hint p) (hint p₀)]
  refine lt_of_le_of_lt (norm_setIntegral_le_of_norm_le_const hfin fun g _ => (hp g).le) ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

theorem continuous_integral_param : ∀ (D : D7) (V : HSp D), CoCpt V → ∀ (v : Vol V) (P : Type) [TopologicalSpace P] (K : GA D V → P → ℂ), Continuous (Function.uncurry K) → (∀ γ ∈ GQ V, ∀ g p, K (γ * g) p = K g p) → (∀ p, IntegrableOn (fun g => K g p) v.𝓕 v.μ) ∧ (Continuous fun p => ∫ g in v.𝓕, K g p ∂v.μ) ∧ ∀ p₀, ∃ C : ℝ, ∀ᶠ p in nhds p₀, ∀ g, ‖K g p‖ ≤ C := by
  intro D V hV v P _ K hK hinv
  obtain ⟨C, hC, hcov⟩ := hV
  have hcov' : ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c := fun h => by
    obtain ⟨γ, hγ, hc⟩ := hcov h
    exact ⟨γ⁻¹, inv_mem hγ, γ * h, hc, by rw [inv_mul_cancel_left]⟩
  have hcont : ∀ p, Continuous fun g => K g p := fun p => hK.comp (continuous_id.prodMk continuous_const)
  have hint : ∀ p, IntegrableOn (fun g => K g p) v.𝓕 v.μ := fun p =>
    GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain V v.μ v.𝓕 C v.haar v.fund hC hcov' _ (hcont p)
      fun γ hγ h => hinv γ hγ h p
  have hfin : v.μ v.𝓕 < ⊤ := by
    have h1 := GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain V v.μ v.𝓕 C v.haar v.fund hC hcov'
      (fun _ => (1 : ℂ)) continuous_const fun _ _ _ => rfl
    simpa using (integrableOn_const_iff (C := (1 : ℂ))).1 h1
  have hcl : ∀ p₀, ∀ ε : ℝ, 0 < ε → ∀ᶠ p in nhds p₀, ∀ g, ‖K g p - K g p₀‖ < ε := fun p₀ ε hε => by
    filter_upwards [eventually_close K hK hC p₀ hε] with p hp g
    obtain ⟨γ, hγ, hc⟩ := hcov g
    have := hp _ hc
    rwa [hinv γ hγ, hinv γ hγ] at this
  refine ⟨hint, continuous_setIntegral_of_unif v.μ v.𝓕 hfin K hint hcl, fun p₀ => ?_⟩
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (hcont p₀).continuousOn
  refine ⟨M + 1, ?_⟩
  filter_upwards [hcl p₀ 1 one_pos] with p hp g
  obtain ⟨γ, hγ, hc⟩ := hcov g
  have h0 := hM _ hc
  simp only [hinv γ hγ] at h0
  have := norm_sub_norm_le (K g p) (K g p₀)
  linarith [hp g]

end GlobalTheory.CocompactParam
end
