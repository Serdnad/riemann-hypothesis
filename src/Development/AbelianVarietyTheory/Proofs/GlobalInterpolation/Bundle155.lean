module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaStepDistributionEquivariantRational
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle152
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle146
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevelPrimePointModelRealisation
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeightsranchOne
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle120
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle153
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle116
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle115
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle149
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemClosureIff
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle144
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle143
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.cm_base_theta_tensor_power_translates_integral : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ (N N' : ℕ) (s : VC D N N'), TorsPrime D q (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) s → LatInt ι (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (U D B.tor s (B.thZero N N')) := by
  first | exact @GlobalTheory.MomN.latInt_U_thZero | exact GlobalTheory.MomN.latInt_U_thZero | (intros; apply GlobalTheory.MomN.latInt_U_thZero <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT

theorem _root_.GlobalTheory.T.thetaStepDistribution_equivariant_rational : ∀ (Z : Dat) (H : D7) (s : Seam H Z.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu)) (u : Z.Pr.Word) (i : ℕ), i < Z.R.m → Hyp Z s cc δ χ cD sel S mu cst u → B.EqP χ → B.VecP χ → MuqTie Z.Ch sel mu cst → (∀ N N' c x, InRange (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) c N N' x → ∀ m : DVar Z.X.Tau (Z.R.N i) (Z.R.N (i + 1)) →₀ ℕ, (∀ τ, (GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.degAt m τ : ℤ) = GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.degNu (Z.W.lamTrue u i) (nuLast Z.W u i) τ) → ∃ k : Z.X.K, (ambOf s B χ cD).σ₀ k = ((ambOf s B χ cD).chiF _ _ N N')⁻¹ * jetC (ambOf s B χ cD).cD ((ambOf s B χ cD).thInd (Sall sel mu u) N N' c x) m) → RatStep Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) := by
  first | exact @GlobalTheory.KerT.RatLaw.ratStep | exact GlobalTheory.KerT.RatLaw.ratStep | (intros; apply GlobalTheory.KerT.RatLaw.ratStep <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.poisson_summation_adelic_tuples : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ → Decay (Fo ψ ν a Φ) → th (Fo ψ ν a Φ) = th Φ := by
  first | exact @GlobalTheory.SWQ.poisson_summation | exact GlobalTheory.SWQ.poisson_summation | (intros; apply GlobalTheory.SWQ.poisson_summation <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

theorem _root_.GlobalTheory.T.trueChainKernels_bound_levelPrimePlaces : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments → GlobalTheory.Published.InducedSimpleLowestAlcove → ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) → ∀ i, i < B.R.m → Dat.KerP (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  exact @GlobalTheory.LvT.Built.TrueLaws.kerP
end

section

noncomputable section

namespace GlobalTheory.PerQ.Co

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem coP_PtT_eq_blk : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ φ ∈ ((I.tw l l0 Z).fm u a).Fi (I.rec7 l Z).R.m, ∀ c, GlobalTheory.PerQ.Co.coP I u a w (GlobalTheory.PerQ.PtT (I.rec7 l Z) u a φ) c = Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ) (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ)) (GlobalTheory.PerQ.Co.coM I u a w c (φ (((I.tw l l0 Z).fm u a).til c))) := by
  intro B X I hI l Z l0 u a w φ hφ c
  have hV : φ ((I.perIn u a).tilC c) ∈ ValC (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (lamT (B.hcW u) B.R.m) := (hφ _).1
  have hT : ((I.stp u a B.R.m).trTo B.fields.emb B.embLL (I.perIn u a).b0 ((I.perIn u a).tilPt c)) (φ ((I.perIn u a).tilC c)) ∈
      ValC (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (lamT (B.hcW u) B.R.m) :=
    GlobalTheory.LvT.Built.RealM.trFr_mem _ _ _ _ _ hV
  obtain ⟨F, hF⟩ := (GlobalTheory.TilClass.mem_ValC_iff _ _ _ _).1 hT
  have hW := fun τ => GlobalTheory.T.trueWeights_eq_descentShiftedWeights_interlace I hI l Z u a τ
  have hS := GlobalTheory.T.localBasisRepLattice_integralCoords_spec I hI l u a w c
  show actP (I.perIn u a).sgT (invTrK ((embGL (embAt B.embLL B.fields.emb)) (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹))
      (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1))
        (fnOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) 1
          ((I.perIn u a).br B.fields.emb B.embLL (B.hcW u)
            (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (lamT (B.hcW u) B.R.m)) (fr0 B.fields.emb B.embLL (B.R.N B.R.m))
              (((I.stp u a B.R.m).trTo B.fields.emb B.embLL (I.perIn u a).b0 ((I.perIn u a).tilPt c)) (φ ((I.perIn u a).tilC c))))))) =
    Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ B.R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ) (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ))
      (actP (lamT (B.hcW u) B.R.m) (invTrK ((embGL (embAt B.embLL B.fields.emb)) (GlobalTheory.PerQ.Co.bM I u a w c)⁻¹))
        (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (lamT (B.hcW u) B.R.m)) (fr0 B.fields.emb B.embLL (B.R.N B.R.m))
          (((I.stp u a B.R.m).trTo B.fields.emb B.embLL (I.perIn u a).b0 ((I.perIn u a).tilPt c)) (φ ((I.perIn u a).tilC c)))))

  rw [← hF, GlobalTheory.TilClass.polOf_fnOf_one, GlobalTheory.TilClass.polOf_fnOf_one]
  have hlam : Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u = lamT (B.hcW u) B.R.m := funext fun τ => (hW τ).1
  have hsg : Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u = (I.perIn u a).sgT := funext fun τ => (hW τ).2.1
  refine Eq.trans ?_ (GlobalTheory.Proof.FockBlockMonotone.blk_brOne_eq (ι := B.fields.Tau) (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ B.R).symm _ _ _).symm
  rw [hlam, hsg]
  have key := GlobalTheory.BranchBlock.rhoVr_brAt_eq_brStd (embAt B.embLL B.fields.emb) (N_m_succ B.R) (lamT (B.hcW u) B.R.m)
    (I.perIn u a).sgT (fun τ => (hW τ).2.2.1) (fun τ => (hW τ).2.2.2.1) (I.perIn u a).tz _ _ hS.2.1 hS.2.2.1 F
  exact congrArg Subtype.val key

end GlobalTheory.PerQ.Co

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ.Co.PtInt

theorem natW_sgT {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (τ : B.fields.Tau) :
    ((I.perIn u a).sgT τ).natW = ((I.perIn u a).sg τ).natW := by
  funext i
  simp only [DomWeight.natW, PerIn.sgT, Col2.shW, DomWeight.detShift]
  split_ifs with h
  · congr 1
    ring
  · exact absurd i.2 (by omega)

theorem invTrK_bc {E K ι : Type} [Field E] [Field K] (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ} (γ : GL (Fin n) E) :
    (fun τ => Formalism.UG.bc σ (invTrK (embGL emb γ) τ)) = invTrK (embGL (embAt σ emb) γ) := by
  funext τ
  ext a b
  have h1 := GlobalTheory.LvT.BuiltChain.invTrK_embGL_apply emb γ τ a b
  have h2 := GlobalTheory.LvT.BuiltChain.invTrK_embGL_apply (embAt σ emb) γ τ a b
  rw [h2]
  show σ (((invTrK (embGL emb γ) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b) = _
  rw [h1]
  rfl

end GlobalTheory.PerQ.Co.PtInt

theorem GlobalTheory.PerQ.Co.PtInt.exists_mem_SP_of_coP_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ z ∈ ((I.tw l l0 Z).fm u a).ptC, (∀ c, GlobalTheory.PerQ.Co.coP I u a w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w ((I.rec7 l Z).fm u).sg) → ∃ y ∈ ((I.tw l l0 Z).fm u a).SP w, ((I.tw l l0 Z).fm u a).ptEmb y = z := by
  intro B X I hI l Z l0 u a w z hz hco
  have hOk : (I.perIn u a).S'.Ok := (l.per u a).step
  have hz' : z ∈ (I.perIn u a).S'.Fi B.fields.emb B.embLL (I.perIn u a).sgT := hz
  have key : ∀ c : (I.perIn u a).S'.Cl, ∃ v : Formalism.L2.DIV.VV B.fields.K (I.perIn u a).sgT,
      z c = evV B.fields.emb (1 : Matrix _ _ B.fields.E) (I.perIn u a).sgT B.embLL v ∧
      v ∈ locW B.places w (delAtr B.fields.emb (I.perIn u a).sgT ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c))) := by
    intro c
    obtain ⟨P, hP, hPz⟩ := (hz' c).1
    obtain ⟨G, hG, hGe⟩ := (GlobalTheory.LvT.Built.ValLat.mem_intSpan_iff (I.rec7 l Z) w _ (I.perIn u a).sgT
      (fun τ => (GlobalTheory.PerQ.Co.PtInt.natW_sgT I u a τ).symm) _).1 (hco c)
    have hGV : G ∈ Formalism.L2.DIV.VV B.fields.K (I.perIn u a).sgT := GlobalTheory.LvT.Built.ValLat.mem_VV_of_locP _ _ hG
    have hspec := GlobalTheory.T.localBasisRepLattice_integralCoords_spec I hI l u a w c
    refine ⟨rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c) ⟨G, hGV⟩, ?_, ?_⟩
    · rw [← hPz]
      show fnOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) 1 P =
        fnOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) 1
          (MvPolynomial.map B.embLL (rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c) ⟨G, hGV⟩).1)
      congr 1
      have e1 : (rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c) ⟨G, hGV⟩).1 =
          actP (I.perIn u a).sgT (invTrK (embGL B.fields.emb (GlobalTheory.PerQ.Co.bP I u a w c))) G := rfl
      rw [e1]
      have e3 := GlobalTheory.LvT.Built.ValLat.map_actP B.embLL (I.perIn u a).sgT
        (invTrK (embGL B.fields.emb (GlobalTheory.PerQ.Co.bP I u a w c))) G
      rw [GlobalTheory.PerQ.Co.PtInt.invTrK_bc] at e3
      refine Eq.trans ?_ e3.symm
      refine Eq.trans ?_ (congrArg (actP (I.perIn u a).sgT
        (invTrK (embGL (embAt B.embLL B.fields.emb) (GlobalTheory.PerQ.Co.bP I u a w c)))) hGe)
      show P = actP (I.perIn u a).sgT (invTrK (embGL (embAt B.embLL B.fields.emb) (GlobalTheory.PerQ.Co.bP I u a w c)))
        (actP (I.perIn u a).sgT (invTrK (embGL (embAt B.embLL B.fields.emb) (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹))
          (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT)
            (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (z c)))
      rw [← polyAction_mul, map_inv, map_inv, mul_inv_cancel, polyAction_one₂, ← hPz]
      have h := polOf_fnOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT)
        (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) P
      have e : (fun τ => ((fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)).1 τ)⁻¹) = 1 := funext fun τ => inv_one
      rw [e] at h
      exact h.symm
    · have hinv : rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹
          (rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c) ⟨G, hGV⟩) = ⟨G, hGV⟩ := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      rw [GlobalTheory.T.mem_locW_delAtr_iff' B.fields.emb B.embLL B.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq (I.perIn u a).sgT
        (I.perIn u a).sg (GlobalTheory.PerQ.Co.PtInt.natW_sgT I u a) _ (hOk.lsh_full_lat c.1 _) w _ hspec.1, hinv]
      have h := hco c
      rw [hGe] at h
      exact h
  choose v hv1 hv2 using key
  obtain ⟨y, hy1, hy2⟩ := GlobalTheory.T.exists_hermitianForm_descent_coefficientField B.fields.emb B.embLL (I.perIn u a).S' (I.perIn u a).sgT (l.fmL u a).famP z hz' v hv1
  refine ⟨y, ?_, hy2⟩
  show y ∈ locW B.places w ((I.perIn u a).S'.hlat B.fields.emb (I.perIn u a).sgT (l.fmL u a).famP).L
  rw [GlobalTheory.T.mem_locW_hlat_iff' B.fields.emb B.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq (I.perIn u a).S' (I.perIn u a).sgT
    (l.fmL u a).famP hOk w y]
  intro c
  rw [hy1 c]
  exact hv2 c
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

theorem _root_.GlobalTheory.T.autFormDefiniteUnitary_eq_sum_polynomial_mul_autForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : UA E n → ℂ), IsAutFormU φ → ∃ (m : ℕ) (p : Fin m → infU E n → ℂ) (e : Fin m → UA E n → ℂ), (∀ i, p i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j} ∧ IsAutFormU (e i)) ∧ ∀ (k : infU E n) (g : UA E n), φ (g * k) = ∑ i, p i k * e i g := by
  first | exact @GlobalTheory.UnitaryDecomp.exists_poly_mul_autForm | exact GlobalTheory.UnitaryDecomp.exists_poly_mul_autForm | (intros; apply GlobalTheory.UnitaryDecomp.exists_poly_mul_autForm <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

theorem _root_.GlobalTheory.T.exists_definiteUnitary_function_polynomial_mul_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (m : ℕ) (p : Fin m → infU E n → ℂ) (e : Fin m → finU (E := E) (n := n) → ℂ), (∀ i, p i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) → (∀ i, ∃ V : Subgroup (finU (E := E) (n := n)), IsOpen (V : Set (finU (E := E) (n := n))) ∧ ∀ u ∈ V, ∀ g, e i (g * u) = e i g) → ∃ φ : UA E n → ℂ, Continuous φ ∧ IsOpen {k : finU (E := E) (n := n) | RU E n k φ = φ} ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)) ∧ ∀ (g : finU (E := E) (n := n)) (k : infU E n), φ (g.1 * k.1) = ∑ i, p i k * e i g := by
  first | exact @GlobalTheory.UnitaryBC.exists_fun_of_poly_smooth | exact GlobalTheory.UnitaryBC.exists_fun_of_poly_smooth | (intros; apply GlobalTheory.UnitaryBC.exists_fun_of_poly_smooth <;> assumption)
end
