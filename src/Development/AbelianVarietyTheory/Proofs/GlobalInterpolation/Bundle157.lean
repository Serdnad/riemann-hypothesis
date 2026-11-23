module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousBdGen
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle056
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle045
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle146
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle098
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteQuotOfReps
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle089
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle147
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle088
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle081
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissibleAdjointRationalPointPadicMatrix
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle134
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle112
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle094
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle092
public import Formalism.LocalToGlobal.Columns.Bundle038
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle156
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle155
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle037
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle038
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle124
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle061
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle064
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntStd
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle150
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle118
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
import Std.Tactic.BVDecide.Normalize.BitVec
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

section

open NumberField IsDedekindDomain

noncomputable section

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT
open GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree (degAt degNu)

namespace GlobalTheory.ChainTheta

section Step

variable {X : Fields} (A : Amb X) {a b : ℕ} (Sa SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
  (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)

theorem thDistC_add_deg (hadd : A.IndAdd a b Sa D) (hsm : A.IndSmooth a b Sa D)
    (hrat : ∀ N N' c x, InRange Sa D c N N' x → ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, (_root_.GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.degAt m τ : ℤ) = degNu lam n τ) →
      ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sa N N' c x) m)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB)
    (c c' : ℕ) (x : HomE X.E a b) (hc : 0 < c) (hc' : 0 < c') (hR : InRange Sa D (c * c') N N' x) :
    thDistC A Sa SB D sel mU mI lam lam' n N fr N' fr' c x =
      latSum (mulLat c (homAt Sa N N')) (mulLat (c * c') (homAt Sa N N')) fun y =>
        thDistC A Sa SB D sel mU mI lam lam' n N fr N' fr' (c * c') (x + y) := by
  have := latFin X a b Sa N N' c c' hR.1 hR.2.1 hc hc'
  let _ := Fintype.ofFinite
    (↥(mulLat c (homAt Sa N N')) ⧸ (mulLat (c * c') (homAt Sa N N')).comap (mulLat c (homAt Sa N N')).subtype)
  set rep := fun z : ↥(mulLat c (homAt Sa N N')) ⧸ (mulLat (c * c') (homAt Sa N N')).comap (mulLat c (homAt Sa N N')).subtype =>
    ((Function.surjInv (Submodule.Quotient.mk_surjective
      ((mulLat (c * c') (homAt Sa N N')).comap (mulLat c (homAt Sa N N')).subtype)) z :
      ↥(mulLat c (homAt Sa N N'))) : HomE X.E a b) with hrep
  have hRz : ∀ z, InRange Sa D (c * c') N N' (x + rep z) := fun z => hR.add (Subtype.coe_prop _)
  have h1 : A.thInd Sa N N' c x = fun w => ∑ z, A.thInd Sa N N' (c * c') (x + rep z) w := by
    funext w
    rw [hadd N N' c c' x hc hc' hR w]
    unfold latSum
    rw [finsum_eq_sum_of_fintype]
  have hJ : jetOp lam lam' (A.jetK Sa N N' c x) n =
      jetOp lam lam' (fun m => ∑ z, A.jetK Sa N N' (c * c') (x + rep z) m) n := by
    refine GlobalTheory.JetIdentity.jetOp_congr lam lam' n _ _ fun m hm => ?_
    have h2 : derivAt0 (A.thInd Sa N N' c x) m = ∑ z, derivAt0 (A.thInd Sa N N' (c * c') (x + rep z)) m := by
      unfold derivAt0
      rw [h1, iteratedFDeriv_sum (fun z _ => hsm N N' (c * c') (x + rep z) (hRz z) _)]
      rw [Finset.sum_apply, _root_.sum_apply]
    choose k hk using fun z => hrat N N' (c * c') (x + rep z) (hRz z) m hm
    have h3 : (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sa N N' c x) m = A.σ₀ (∑ z, k z) := by

      rw [map_sum]
      simp only [hk]
      unfold jetC
      rw [h2, Finset.mul_sum, Finset.mul_sum]
    unfold Amb.jetK
    rw [h3, desc_map]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← hk z, desc_map]
  unfold latSum
  rw [finsum_eq_sum_of_fintype]
  unfold thDistC
  rw [if_pos ⟨(Dvd.intro _ rfl).trans hR.2.2.2.1, hR.2.2.2.2⟩, hJ, Formalism.L2.Ker.jetOp_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  exact (if_pos ⟨hR.2.2.2.1, mem_divLat_add D c _ hR.2.2.2.2 (Subtype.coe_prop _)⟩).symm

end Step

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (A : Amb X) (u : Pr.Word)

theorem stepC_ok_deg (i : ℕ) (hi : i < R.m) (j : ℕ) (hT : 0 < Pr.T u) (hq : MuqTie Ch sel mu cst)
    (hL : A.LaHyp (R.N i) (R.N j) (Sall sel mu u)) (hE : A.ESmooth (R.N i) (R.N j))
    (hrat : ∀ N N' c x, InRange (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) c N N' x →
      ∀ m : DVar X.Tau (R.N i) (R.N j) →₀ ℕ, (∀ τ, (_root_.GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.degAt m τ : ℤ) = degNu (W.lamTrue u i) (nuLast W u i) τ) →
      ∃ k : X.K, A.σ₀ k = (A.chiF _ _ N N')⁻¹ * jetC A.cD (A.thInd (Sall sel mu u) N N' c x) m)
    (hR : RatStep W Ch sel mu cst A u i j) :
    ThDist.Ok (stepC W Ch sel mu cst A u i (W.lamTrue u j)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      ((rhoVr X.emb (W.lamTrue u i)).comp (ufGL X.E (R.N i))) ((rhoVr X.emb (W.lamTrue u j)).comp (ufGL X.E (R.N j)))
      (rhoS Ch sel mu i) (rhoT Ch sel mu i) := by
  have hD := modulus_pos sel mu cst u hT
  unfold RatStep at hR
  rw [← stepC_eq_stepT W Ch sel mu cst hq A u i hi] at hR
  exact
    { cong := fun N fr N' fr' c x x' _ _ h => thDistC_cong A _ _ sel _ _ _ _ _ _ N fr N' fr' c x x' h
      add := fun N fr N' fr' c c' x hN hN' hc hc' hd hx =>
        thDistC_add_deg A _ _ _ sel _ _ _ _ _
          (indAdd_of A _ _ _ _ hD (latFin X _ _ _) (indTieD_of_la A _ _ _ _ hD hL)) (indSmooth_of A _ _ _ _ hE) hrat
          N fr N' fr' c c' x hc hc' ⟨hN, hN', Nat.mul_pos hc hc', hd, hx⟩
      equiv := thDistC_equiv A _ _ sel _ _ _ _ _ _ hD _ _ hR
      det := fun N fr N' fr' c x κ κ' _ _ =>
        thDistC_det A _ _ sel _ _ _ _ _ _ _ _ (muDetLaw_chain Ch sel mu cst i _) (muDetLaw_chain Ch sel mu cst i _)
          (unitInv_rho Ch sel mu i) N fr N' fr' c x κ κ' }

end Chain

theorem chTh_ok_of_hyp {Z : Dat} {H : D7} {s : Seam H Z.X} {cc : Ideal (𝓞 H.host.K)} {δ : ℂ} (B : Base H cc δ) {χ : TaylorLogMetric.IdE H → ℂ}
    {cD : H.what₂.Tau → ℂ} {sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)} {S : Set ℕ}
    {mu : Tup Z.X.F Z.X.E Z.X.K S} {cst : LocCst Z.X (rowSG Z.Pr sel mu)} {u : Z.Pr.Word} {m2 : ℕ} (hm : Z.R.m = m2 + 2)
    (h : Hyp Z s cc δ χ cD sel S mu cst u) (hE : B.EqP χ) (hV : B.VecP χ) (hq : MuqTie Z.Ch sel mu cst)
    (hJ : ∀ i, i < Z.R.m → ∀ N N' c x, InRange (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) c N N' x →
      ∀ m : DVar Z.X.Tau (Z.R.N i) (Z.R.N (i + 1)) →₀ ℕ, (∀ τ, (_root_.GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.degAt m τ : ℤ) = degNu (Z.W.lamTrue u i) (nuLast Z.W u i) τ) →
      ∃ k : Z.X.K, (ambOf s B χ cD).σ₀ k = ((ambOf s B χ cD).chiF _ _ N N')⁻¹ *
        jetC (ambOf s B χ cD).cD ((ambOf s B χ cD).thInd (Sall sel mu u) N N' c x) m) :
    ChTh.Ok (Ch := Z.Ch) cst (chTh Z.W Z.Ch sel mu cst (ambOf s B χ cD) u m2) := by
  have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes Z.X Z.Pr sel S mu u h.ok.fields h.ok.primes h.isSel h.T_mem h.g_mem
  have key : ∀ i j, i < Z.R.m → j = i + 1 →
      ThDist.Ok (stepC Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (Z.W.lamTrue u j)) (Sall sel mu u)
        (cAof sel mu cst * cBof sel mu cst u) ((rhoVr Z.X.emb (Z.W.lamTrue u i)).comp (ufGL Z.X.E (Z.R.N i)))
        ((rhoVr Z.X.emb (Z.W.lamTrue u j)).comp (ufGL Z.X.E (Z.R.N j))) (rhoS Z.Ch sel mu i) (rhoT Z.Ch sel mu i) := by
    rintro i _ hi rfl
    obtain ⟨hL, hS⟩ := GlobalTheory.T.normalisedFamily_latticeHyp_and_smooth H Z.X s cc δ B χ cD (Z.R.N i) (Z.R.N (i + 1)) h.ok.fields h.ana.1 h.ana.2.2.1 h.ana.2.2.2.1 hV
      (GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.even_N _ _) (GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.even_N _ _)
    exact stepC_ok_deg Z.W Z.Ch sel mu cst _ u i hi (i + 1) (h.ok.primes.T_prime u).pos hq
      ⟨hL.1, hL.2.1, fun P hP => (bad P hP).1,
        fun P hP => GlobalTheory.PeriodIdealUnit.locP_AA_eq_one Z.X H s cc δ B χ cD P (bad P hP).2.1 (bad P hP).2.2.1 (h.cop P hP),
        hL.2.2.2.2⟩ hS (hJ i hi)
      (GlobalTheory.T.thetaStepDistribution_equivariant_rational Z H s cc δ B χ cD sel S mu cst u i hi h hE hV hq (hJ i hi))
  exact ⟨fun i hi => key i (i + 1) (by omega) rfl, key (m2 + 1) Z.R.m (by omega) hm⟩


open GlobalTheory.Mem GlobalTheory.Mem.Col2 in
theorem chTh_ok_of_colIn (B : GlobalTheory.Mem.Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) {X : PreX B.toPre} (I : ColIn B X) (h : I.Ok) (hJ : I.JetsIn)
    (hE : (I.J.toRec B C W V S N G).EqP I.chi) (hV : (I.J.toRec B C W V S N G).VecP I.chi)
    (a : I.ι) (u : B.Word) (m2 : ℕ) (hm : B.R.m = m2 + 2) :
    ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u m2) := by
  have h1 := chTh_ok_of_hyp (Z := I.dat) (I.J.toRec B C W V S N G) hm (hyp_of_colIn B C W V S N G I h a u) hE hV
    (muqTie_of_ok _ _ _ _ _ (h.idx_ok a)) (by
      rw [← AmbIn.amb_eq_ambOf]
      intro i hi L L' c x hx m hd
      refine hJ.exists_eq hi hx fun τ => ?_
      rw [monoDeg_eq_sum]
      exact (hd τ).trans (GlobalTheory.MoveCompare.degNu_eq (Pr := B.primes X) B.wts u hi τ))
  rw [← AmbIn.amb_eq_ambOf] at h1
  exact h1


open GlobalTheory.Mem GlobalTheory.Mem.Col2 in
theorem chTh_ok_of_colIn' (B : GlobalTheory.Mem.Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) {X : PreX B.toPre} (I : ColIn B X) (h : I.Ok) (hJ : I.JetsIn)
    (hE : (I.J.toRec B C W V S N G).EqP I.chi) (hV : (I.J.toRec B C W V S N G).VecP I.chi) (a : I.ι) (u : B.Word) :
    ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) :=
  chTh_ok_of_colIn B C W V S N G I h hJ hE hV a u _ h.hm

end GlobalTheory.ChainTheta
end
end

section

noncomputable section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomN

theorem contDiff_U {D : D7} {N N' : ℕ} (T : Tor D) (t : VC D N N') {G : VC D N N' → ℂ} (hG : ContDiff ℂ ⊤ G) :
    ContDiff ℂ ⊤ (U D T t G) := by
  have hH : ContDiff ℂ ⊤ fun z : VC D N N' => Hf D T z t := by
    unfold Hf
    refine ContDiff.div_const ?_ _
    refine ContDiff.sum fun τ _ => ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
    refine ContDiff.mul ?_ contDiff_const
    fun_prop
  unfold U
  refine ContDiff.mul (hG.comp (contDiff_id.add contDiff_const)) ?_
  exact ContDiff.cexp ((contDiff_const.mul hH).sub contDiff_const)

theorem transPrime_int : (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ) → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ t : VC D N N', TorsPrime D q (La D B.tor L L') t → LatInt ι (Ω / ι δ₀) (La D B.tor L L') (U D B.tor t (B.eNat χ N N' L L')) := by
  intro hEq D cc δ B hcc hδ q _ hq2 hsplit hcop ι δ₀ θ Ω hPer χ hχ N N' L L' hA t ht
  letI := D.host.cmStar
  obtain ⟨γ, γ', M, M', hAM, hE, hE', rfl, rfl⟩ := GlobalTheory.T.weakApproximation_unitaryLattices_splitPrime D q hq2 hsplit N N' L L' hA
  obtain ⟨hN, hN', hSM, hSM'⟩ := id hAM
  have hcov : pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
      (B.eNat χ N N' M M') =
      B.eNat χ N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M') :=
    (hEq D cc δ B χ hcc hδ hχ).1 N N' ⟨M, hSM⟩ ⟨M', hSM'⟩ hN hN' γ γ'
  obtain ⟨g, hg, hU⟩ := GlobalTheory.T.unitaryPairPullback_lattices_translates D cc δ N N' γ γ' M M'
  have ht' : TorsPrime D q (La D B.tor M M') (g t) := by
    obtain ⟨n, hn, hc, hm⟩ := ht
    refine ⟨n, hn, hc, ?_⟩
    have := hg _ hm
    rwa [map_nsmul] at this
  let lam : Qbar →+* ℂ_[q] := (ι : ℂ →+* ℂ_[q]).comp (algebraMap Qbar ℂ)
  obtain ⟨m, c, s, hc, hs, heq⟩ :=
    GlobalTheory.T.translate_normalized_vector_integral_comb_tensor_power D cc δ B hcc hδ χ hχ q lam N N' M M' hAM hE hE' (g t) ht'
  have hzero : ∀ k, LatInt ι (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
      (U D B.tor (s k) (B.thZero N N')) := fun k =>
    GlobalTheory.T.cm_base_theta_tensor_power_translates_integral D cc δ B hcc hδ q hq2 hsplit hcop ι δ₀ θ Ω hPer N N' (s k) (hs k)
  have hd : ContDiff ℂ ⊤ (B.thZero N N') :=
    AnalyticOnNhd.contDiff (B.thZeroMem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ) N N').1
  have hsm : ∀ k, ContDiff ℂ ⊤ (U D B.tor (s k) (B.thZero N N')) := fun k => contDiff_U _ _ hd
  have hcn : ∀ k, ‖ι (c k)‖ ≤ 1 := by
    intro k
    obtain ⟨h1, h2⟩ := hc k
    have e : lamC lam (c k) = ι (c k) := by
      unfold lamC
      rw [dite_eq_left h1]
      rfl
    rw [← e]
    exact h2
  have hsum := (GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum q ι (VC D N N') (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))).2
    (Fin m) Finset.univ c (fun k => U D B.tor (s k) (B.thZero N N')) (fun k _ => hsm k) (fun k _ => hcn k)
    (fun k _ => hzero k)
  have hGs : ContDiff ℂ ⊤ fun z => ∑ k, c k * U D B.tor (s k) (B.thZero N N') z :=
    ContDiff.sum fun k _ => contDiff_const.mul (hsm k)
  obtain ⟨a, ha, hsM, hMs⟩ := hE
  obtain ⟨b, hb, hsM', hMs'⟩ := hE'
  have hpull := GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι (VC D N N') (VC D N N') (Ω / ι δ₀)
    (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
    (La D B.tor (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
      (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M')) g _ hGs
    (fun x hx => ⟨a * b, Nat.Coprime.mul_left ha hb,
      Formalism.L2.KerInert.ISd.La_smul cc δ a b hsM hMs' (hg x hx)⟩) hsum
  rw [← hcov, show U D B.tor t (pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E)
      (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.eNat χ N N' M M')) =
      fun z => U D B.tor (g t) (B.eNat χ N N' M M') (g z) from hU t _, heq]
  exact hpull

end GlobalTheory.MomN
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ

theorem fourier_inversion : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ)
    (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a →
    ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ → Decay (Fo ψ ν a Φ) → Decay (Fo ψ ν a (Fo ψ ν a Φ)) →
      Fo ψ ν a (Fo ψ ν a Φ) = Da (-1) Φ := by
  intro F _ _ N ψ lam ν a hC Φ hΦ hFΦ hFFΦ
  have hD1 : Decay (Da (-1) Φ) :=
    (GlobalTheory.SWQ.decay_ops F N ψ lam ν a hC Φ hΦ).2.2.1 (-1) isUnit_one.neg
  apply GlobalTheory.T.eq_of_theta_heisenbergTranslates F N ψ lam ν a hC _ _ hFFΦ hD1
  intro x y

  have iΦ := GlobalTheory.SWQ.weil_intertwine F N ψ lam ν a hC Φ
  have iFΦ := GlobalTheory.SWQ.weil_intertwine F N ψ lam ν a hC (Fo ψ ν a Φ)
  have e1 : rho ψ a (-y) x (Fo ψ ν a Φ) = Fo ψ ν a (rho ψ a (-x) (-y) Φ) := by
    have := iΦ.2.2.1 (-y) x
    simpa using this
  have e2 : rho ψ a x y (Fo ψ ν a (Fo ψ ν a Φ)) = Fo ψ ν a (Fo ψ ν a (rho ψ a (-x) (-y) Φ)) := by
    rw [iFΦ.2.2.1 x y, e1]
  have dΨ : Decay (rho ψ a (-x) (-y) Φ) := (GlobalTheory.SWQ.decay_ops F N ψ lam ν a hC Φ hΦ).2.1 _ _
  have dFΨ : Decay (Fo ψ ν a (rho ψ a (-x) (-y) Φ)) := by
    rw [← e1]; exact (GlobalTheory.SWQ.decay_ops F N ψ lam ν a hC _ hFΦ).2.1 _ _
  have dFFΨ : Decay (Fo ψ ν a (Fo ψ ν a (rho ψ a (-x) (-y) Φ))) := by
    rw [← e2]; exact (GlobalTheory.SWQ.decay_ops F N ψ lam ν a hC _ hFFΦ).2.1 _ _
  rw [e2, GlobalTheory.T.poisson_summation_adelic_tuples F N ψ lam ν a hC _ dFΨ dFFΨ, GlobalTheory.T.poisson_summation_adelic_tuples F N ψ lam ν a hC _ dΨ dFΨ]

  have e3 : rho ψ a x y (Da (-1) Φ) = Da (-1) (rho ψ a (-x) (-y) Φ) := by
    have := iΦ.2.1 (-1) (-1) x y (by norm_num)
    simpa using this
  rw [e3]
  have e4 : (Da (-1 : AF F) (rho ψ a (-x) (-y) Φ) : (Fin N → AF F) → ℂ) =
      Da (algebraMap F (AF F) (-1)) (rho ψ a (-x) (-y) Φ) := by simp
  rw [e4, (GlobalTheory.SWQ.weil_intertwine F N ψ lam ν a hC (rho ψ a (-x) (-y) Φ)).2.2.2.2 (-1) (by norm_num)]

end GlobalTheory.SWQ
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

noncomputable section

namespace GlobalTheory.LvT.Built.TrueLaws

open _root_.Formalism.L2.Col

local instance starFields (B : Base) : StarRing B.fields.E := B.fields.starE

theorem kerBar : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments → GlobalTheory.Published.InducedSimpleLowestAlcove → ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) → ∀ i, i < B.R.m → Dat.KerBar (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  intro hJM hP B X I h hJ l Z u a hth i hi
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hA : ColIn.A I = ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J)
      (ColIn.chi I) I.J.cD := by
    rw [ColIn.A, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G]
  have hH := GlobalTheory.KerT.hyp_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h a u
  have hJa := GlobalTheory.KerT.jetsAll_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h hJ a u hi
  have hAl := GlobalTheory.KerT.alcoveAt_of_ok I.dat hH.ok u (i + 1) (Nat.succ_le_of_lt hi)
  have hRS := GlobalTheory.KerT.ratStep_of_chTh_ok B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob
    (B.R.m - 2) u i I.A hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) hth hi
  rw [hA] at hRS
  have hRT : GlobalTheory.KerT.RatTerm (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a)
      (ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) (ColIn.chi I) I.J.cD)
      u i (i + 1) :=
    GlobalTheory.KerRat.ratTerm_of_ratStep B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) _ u i hX hPr
      h.sel_ok (h.T_mem u) hRS
  have hT := isTerm h u a hi
  intro w hw hseen b b' d d' F hF
  classical
  unfold OverT at hw
  have hw' : (((B.primes X).T u : ℕ) : 𝓞 B.fields.K) ∈ ((I.rec7 l Z).plEq w).asIdeal := by
    have h0 := Formalism.L2.Col.att_resChar_mem (I.rec7 l Z).what₂.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq w
    rw [hw] at h0
    exact h0
  have hs : ¬ seenC (B.primes X) u ((I.rec7 l Z).plEq w) := fun hc => by
    have h0 : decide (seenC (B.primes X) u ((I.rec7 l Z).plEq w)) = false := hseen
    simp [hc] at h0
  have hsb : seenBarC (B.primes X) u ((I.rec7 l Z).plEq w) := (seenC_or_seenBarC hX hPr u _ hw').resolve_left hs
  have hbar : GlobalTheory.KerT.BarTerm (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) (ColIn.chi I) I.J.cD) u i (i + 1)
      ((I.rec7 l Z).plEq w) := GlobalTheory.KerT.Bar.barTerm_of_std I.dat _ (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
    (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hRT ((I.rec7 l Z).plEq w)
    (fun d fr d' fr' Ξ₀ => GlobalTheory.BarStd.barStd hJM hP I.dat _ (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
      (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hJa hAl
      ((I.rec7 l Z).plEq w) hsb d fr d' fr' Ξ₀)
  rw [← hA] at hbar
  obtain ⟨Ξ₀, hbox, hint, hfr, hfr', hk⟩ := hT b b' d d'
  have hk' := hk d d' ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  rw [hk']
  have hF' : F ∈ GlobalTheory.KerT.valAt ((I.rec7 l Z).plEq w) (B.wts.lamTrue u i) d.1.1.deco.1.Lsh := hF
  obtain ⟨y', hy', he⟩ := hbar d.1.1.deco _ d'.1.1.deco _ Ξ₀ hfr hfr' hbox (hint _ hw') F hF'
  refine ⟨y', hy', he.trans ?_⟩
  have e1 : B.fields.f = (I.rec7 l Z).R.f := GlobalTheory.Mem.Base.fields_f B
  rw [e1]
  rfl

end GlobalTheory.LvT.Built.TrueLaws
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localCoords_evaluationLowerRowMap_eq_tensor_branching : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ φ ∈ ((I.tw l l0 Z).fm u a).Fi (I.rec7 l Z).R.m, ∀ c, GlobalTheory.PerQ.Co.coP I u a w (GlobalTheory.PerQ.PtT (I.rec7 l Z) u a φ) c = Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ) (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ)) (GlobalTheory.PerQ.Co.coM I u a w c (φ (((I.tw l l0 Z).fm u a).til c))) := by
  first | exact @GlobalTheory.PerQ.Co.coP_PtT_eq_blk | exact GlobalTheory.PerQ.Co.coP_PtT_eq_blk | (intros; apply GlobalTheory.PerQ.Co.coP_PtT_eq_blk <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_integralHyperplaneForm_of_localCoords_integral : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ z ∈ ((I.tw l l0 Z).fm u a).ptC, (∀ c, GlobalTheory.PerQ.Co.coP I u a w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w ((I.rec7 l Z).fm u).sg) → ∃ y ∈ ((I.tw l l0 Z).fm u a).SP w, ((I.tw l l0 Z).fm u a).ptEmb y = z := by
  first | exact @GlobalTheory.PerQ.Co.PtInt.exists_mem_SP_of_coP_mem | exact GlobalTheory.PerQ.Co.PtInt.exists_mem_SP_of_coP_mem | (intros; apply GlobalTheory.PerQ.Co.PtInt.exists_mem_SP_of_coP_mem <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hyperplaneFormIntegral_localCoords_mem_integralSpan : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ z ∈ ((I.tw l l0 Z).fm u a).ptC, (∃ y ∈ ((I.tw l l0 Z).fm u a).SP w, ((I.tw l l0 Z).fm u a).ptEmb y = z) → ∀ c, GlobalTheory.PerQ.Co.coP I u a w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w ((I.rec7 l Z).fm u).sg := by
  first | exact @GlobalTheory.PtIntCoord.coP_mem_intSpan | exact GlobalTheory.PtIntCoord.coP_mem_intSpan | (intros; apply GlobalTheory.PtIntCoord.coP_mem_intSpan <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastStepIntegralForm_localCoords_mem_integralSpan : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ x ∈ ((I.tw l l0 Z).fm u a).S (I.rec7 l Z).R.m w, ∀ c, GlobalTheory.PerQ.Co.coM I u a w c (((I.tw l l0 Z).fm u a).emb (I.rec7 l Z).R.m x (((I.tw l l0 Z).fm u a).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) := by
  first | exact @GlobalTheory.PerQ.Co.latCo_mem_intSpan | exact GlobalTheory.PerQ.Co.latCo_mem_intSpan | (intros; apply GlobalTheory.PerQ.Co.latCo_mem_intSpan <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

theorem exists_conj_isAutFormU (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ)
    (φ : UA E n → ℂ) (hφ : IsAutFormU φ) :
    ∃ φ' : UA E n → ℂ, IsAutFormU φ' ∧ ∀ g ∈ finU (E := E) (n := n), φ' g = σ (φ g) := by
  obtain ⟨m, p, e, hpe, hdec⟩ := GlobalTheory.T.autFormDefiniteUnitary_eq_sum_polynomial_mul_autForm E n φ hφ
  choose p' hp' hpp using fun i => GlobalTheory.T.exists_conj_polynomial_definiteUnitary_rational E n σ (p i) (hpe i).1
  obtain ⟨hD, -, -, a, b, -, -, hab, -⟩ := GlobalTheory.T.definiteUnitary_realApprox_and_finite_infinite_split E n
  obtain ⟨φ', hc, hl, hk, hv⟩ := GlobalTheory.T.exists_definiteUnitary_function_polynomial_mul_smooth E n m p' (fun i g => σ (e i g.1)) hp' (fun i => by
    refine ⟨
      { carrier := {k : finU (E := E) (n := n) | RU E n k (e i) = e i}
        one_mem' := by simp
        mul_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq] at hx hy ⊢
          rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]
        inv_mem' := fun {x} hx => by
          simp only [Set.mem_setOf_eq] at hx ⊢
          conv_lhs => rw [← hx]
          rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply] }, ?_, ?_⟩
    · exact (hpe i).2.level
    · intro u hu g
      exact congrArg σ (congrFun (show RU E n u (e i) = e i from hu) g.1))
  have key : ∀ γ ∈ ratU E n, ∀ x : UA E n, cInf x = cInf γ → φ' x = σ (φ x) := by
    intro γ hγ x hx
    have h1 : cInf (b x).1 = cInf γ := by
      rw [← hx]
      conv_rhs => rw [hab x, map_mul, show cInf (a x).1 = 1 from (a x).2, one_mul]
    conv_lhs => rw [hab x, hv]

    conv_rhs => rw [hab x, hdec, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hpp i γ hγ _ h1]
  refine ⟨φ', ⟨hc, fun γ hγ g => ?_, hl, hk⟩, fun g hg => key 1 (one_mem _) g (by rw [map_one]; exact hg)⟩
  have hc2 : Continuous fun x => φ' (γ * x) := hc.comp (continuous_const.mul continuous_id)
  refine congrFun (Continuous.ext_on hD hc2 hc ?_) g
  rintro _ ⟨δ, hδ, u, hu, rfl⟩
  have hu' : cInf u = 1 := hu
  change φ' (γ * (δ * u)) = φ' (δ * u)
  rw [key (γ * δ) (mul_mem hγ hδ) _ (by simp only [map_mul, hu', mul_one]),
    key δ hδ _ (by simp only [map_mul, hu', mul_one]), hφ.left γ hγ]

end GlobalTheory.UnitaryBC
end
