module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BadPrimeNormPrimeNeLevelPrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle104
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotDvdCardOfInjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle113
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KAtTopEquiv
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle045
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle328
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle318
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle168
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle145
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle144
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle143
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultipliableEulerFac
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle214
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.FinalEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003

@[expose] public section

section

namespace GlobalTheory.DensityProductClosed

theorem eulerProductOfDensities : GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.EulerProductOfDensities :=
  GlobalTheory.DensityProductCompare.densityProduct_iff.1 GlobalTheory.T.cm_localDensities_productFormula

end GlobalTheory.DensityProductClosed
end

section

namespace GlobalTheory.LvT.Built.Box

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2
open GlobalTheory.ColPeriod GlobalTheory.LvT.Built.IsTerm

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ} {u : Pr.Word}

theorem pow_dvd_cA (P : rowSG Pr sel mu) : qOf P.1 ^ cst.A ∣ cAof sel mu cst :=
  pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun Q : rowSG Pr sel mu => qOf Q.1) (Finset.mem_univ P)) _

theorem intAt_of_locTop (hL : L.Ok Ch sel mu cst G m2) (P : rowSG Pr sel mu) {j : ℕ} (hj : j = R.m)
    (x : HomE X.E (R.N (m2 + 1)) (R.N j)) (y : Sp X.E (R.N (m2 + 1)))
    (h : TopStep.locTop Ch sel mu cst m2 P (castSp X.E (congrArg R.N hj) ∘ₗ x) y ≠ 0) (s : Fin (R.N (m2 + 1))) (l : Fin (R.N j)) :
    IntAt P.1 ((qOf P.1 : X.E) ^ cst.A * x (Pi.single s 1) l) := by
  subst hj
  have hm := hL.hm
  rw [castSp_comp] at h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  have hl2 := l.2
  by_cases hlt : l.1 < R.N R.m - 1
  · have h3 := GlobalTheory.SuppTop.intAt_of_phiTop Ch mu cst.sharp _ hm P.1 _ h1 l.1 s.1 hlt s.2
    have e1 : LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) (Loc.eN X.E (R.N (m2 + 1) + cOf R (m2 + 1)) s.1) =
        Pi.single s 1 := by
      funext t
      simp [LinearMap.funLeft_apply, Loc.eN, Pi.single_apply, Fin.ext_iff]
    simp only [LinearMap.comp_apply, e1] at h3
    have hlt' : l.1 < R.N R.m - 1 + 0 := hlt
    simp only [Loc.atN, dif_pos hlt', prXp, LinearMap.funLeft_apply] at h3
    have h4 := (GlobalTheory.SuppTop.intAt_nat P.1 (qOf P.1 ^ cst.A)).mul h3
    rwa [Nat.cast_pow] at h4
  · have h3 := GlobalTheory.SuppTop.intAt_of_ftY sel mu cst P _ _ h2 s
    have hl3 : R.N R.m - 1 < R.N R.m := by omega
    have hl4 : (⟨R.N R.m - 1, hl3⟩ : Fin (R.N R.m)) = l := Fin.ext (by simp only; omega)
    simp only [LinearMap.comp_apply, atNL, dif_pos hl3, LinearMap.proj_apply, hl4] at h3
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hL.cst_ok.M_le_A
    have h4 := (GlobalTheory.SuppTop.intAt_nat P.1 (qOf P.1 ^ k)).mul h3
    rw [Nat.cast_pow, ← mul_assoc, ← pow_add] at h4
    rwa [hk]

theorem intAt_of_xiAt (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < R.m) {b : Idx sel mu L i} {b' : Idx sel mu L (i + 1)}
    {p : PtAt R sel mu cst u i} {p' : PtAt R sel mu cst u (i + 1)} {x : HomE X.E (R.N i) (R.N (i + 1))}
    (hx : xiAt Ch sel mu cst L u i b b' p p' x ≠ 0) (P : rowSG Pr sel mu) (s : Fin (R.N i)) (l : Fin (R.N (i + 1))) :
    IntAt P.1 ((qOf P.1 : X.E) ^ cst.A * inFr (frsF sel mu p.1.1 P) (frsF sel mu p'.1.1 P) x (Pi.single s 1) l) := by
  have hm := hL.hm
  rcases lt_trichotomy (i + 2) R.m with h | h | h
  · rw [xiAt_entry Ch sel mu cst L h (b.some_get (by omega)).symm (b'.some_get (by omega)).symm] at hx
    exact hL.xiSupp i (by omega) _ _ P _
      (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) P (Finset.mem_univ _)) s l
  · obtain rfl : i = m2 := by omega
    rw [xiAt_penultimate_eq_xiCpl1 Ch sel mu cst L h (b.some_get (by omega)).symm] at hx
    exact hL.psiSuppX _ P _ _ (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) P (Finset.mem_univ _)) s l
  · obtain rfl : i = m2 + 1 := by omega
    have h1 : m2 + 1 + 1 = R.m := by omega
    rw [xiAt_last Ch sel mu cst L h1] at hx
    exact intAt_of_locTop hL P h1 _ _ (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) P (Finset.mem_univ _)) s l

theorem inBox_xiAt : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → L.Ok Ch sel mu cst G m2 → i < R.m → (∃ (σ₀ : X.K →+* ℂ) (e : Fin R.m → X.Tau → ℚ) (m0 : Fin R.m → Formalism.L2.Host.HChar X.E) (eta : Formalism.L2.Host.HChar X.E), Ch.Tied σ₀ e m0 eta) → ∀ (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)) (p : PtAt R sel mu cst u i) (p' : PtAt R sel mu cst u (i + 1)), GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.1.1.deco.1.N p'.1.1.deco.1.N (xiAt Ch sel mu cst L u i b b' p p') := by
  classical
  rintro X Pr R Ch sel S mu cst L G m2 u i hX hPr hsel hS hg hL hi ⟨σ₀, e, m0, eta, ht⟩ b b' p p'
  refine ⟨fun x hx P hP y hy => ?_, fun x y hy => ?_⟩
  · change ((cAof sel mu cst : ℕ) : 𝓞 X.E) • x y ∈ _
    have hP' : P ∈ Pr.vT u ∨ P ∈ rowSG Pr sel mu := by
      unfold Sall at hP
      exact Finset.mem_union.1 hP
    rcases hP' with hP | hP
    · exact Submodule.smul_mem _ _ (phiT_of_xiAt_ne_zero Ch sel mu cst L hx ⟨P, hP⟩ y hy).1
    · obtain ⟨k, hk⟩ : qOf P ^ cst.A ∣ cAof sel mu cst :=
        pow_dvd_cA ⟨P, hP⟩
      have h := GlobalTheory.SuppTop.smul_mem_of_inFr P _ _ _ _ (isFrames_frsF p.1.1 ⟨P, hP⟩) (isFrames_frsF p'.1.1 ⟨P, hP⟩)
        (cAof sel mu cst) x (fun s l => by
          have h4 := (GlobalTheory.SuppTop.intAt_nat P k).mul (intAt_of_xiAt hL hi hx ⟨P, hP⟩ s l)
          rw [hk, Nat.cast_mul, Nat.cast_pow, mul_comm _ (k : X.E), mul_assoc]
          exact h4) y hy
      simpa [Nat.cast_smul_eq_nsmul] using h
  · obtain ⟨Φ, hΦ⟩ := exists_local hX hPr hsel hS hL (muqUnit_of_tied hX hPr hsel hS hg hL ht) hi b b'
    obtain ⟨w, hw⟩ := exists_place X.K (hPr.T_prime u)
    rw [(hΦ p p').1, (hΦ p p').1]
    congr 1
    · exact phiT_add _ p'.1.1.deco.2 (T := Pr.T u) (fun Q => T_mem_of_piT_mem hPr u (GlobalTheory.ColPeriod.mem_divs Q.2)) x fun Q =>
        exists_of_mem_mulLat (Dvd.intro _ rfl) hy (Finset.mem_union_left _ Q.2)
    · refine Finset.prod_congr rfl fun P _ => ?_
      have hdv : qOf P.1 ^ cst.B ∣ cBof sel mu cst u :=
        Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ P)) _) _
      obtain ⟨z, hz, rfl⟩ := exists_of_mem_mulLat hdv hy (Finset.mem_union_right _ P.2)
      rw [Nat.cast_pow]
      exact (awayAt_inFr (isFrames_frsF p.1.1 P) (isFrames_frsF p'.1.1 P) ((hΦ p p').2 P w hw)).2 x z hz

end GlobalTheory.LvT.Built.Box
end

section

noncomputable section

namespace GlobalTheory.PerQ.Co

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def bP (u : B.Word) (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl) : GL (Fin (B.R.N B.R.m - 1)) B.fields.E :=
  Classical.epsilon fun g : GL (Fin (B.R.N B.R.m - 1)) B.fields.E =>
    Formalism.L2.Forms.IsLocBasis (B.places.resChar w) ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c) : Set _) g

def bM (u : B.Word) (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl) : GL (Fin (B.R.N B.R.m)) B.fields.E :=
  Classical.epsilon fun g : GL (Fin (B.R.N B.R.m)) B.fields.E =>
    (∀ x, iniH (N_m_succ B.R) ((g : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) =
        ((bP I u a w c : GL (Fin (B.R.N B.R.m - 1)) B.fields.E) : Matrix _ _ B.fields.E) *ᵥ iniH (N_m_succ B.R) x) ∧
      (∀ x, (I.perIn u a).tz * ((g : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) (Br.iL (N_m_succ B.R)) =
        x (Br.iL (N_m_succ B.R))) ∧
      Formalism.L2.Forms.IsLocBasis (B.places.resChar w)
        (((I.chIn u a).S B.R.m).Lsh (I.perIn u a).b0 ((I.perIn u a).tilPt c) : Set _) g

def coP (u : B.Word) (a : I.ι) (w : B.places.Pl) :
    ((I.perIn u a).S'.Cl → Fr B.fields.emb B.embLL (B.R.N B.R.m - 1) → ℂ) →ₗ[ℂ]
      ((I.perIn u a).S'.Cl → MvPolynomial (B.fields.Tau × Fin (B.R.N B.R.m - 1) × Fin (B.R.N B.R.m - 1)) ℂ) :=
  LinearMap.pi fun c =>
    actP (I.perIn u a).sgT (invTrK (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) (bP I u a w c)⁻¹)) ∘ₗ
      polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) ∘ₗ
      LinearMap.proj c

def coM (u : B.Word) (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl) :
    (Fr B.fields.emb B.embLL (B.R.N B.R.m) → ℂ) →ₗ[ℂ]
      MvPolynomial (B.fields.Tau × Fin (B.R.N B.R.m) × Fin (B.R.N B.R.m)) ℂ :=
  actP (lamT (B.hcW u) B.R.m) (invTrK (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) (bM I u a w c)⁻¹)) ∘ₗ
    polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (lamT (B.hcW u) B.R.m)) (fr0 B.fields.emb B.embLL (B.R.N B.R.m)) ∘ₗ
    (((I.chIn u a).S B.R.m).trTo B.fields.emb B.embLL (I.perIn u a).b0 ((I.perIn u a).tilPt c)).toLinearMap

end GlobalTheory.PerQ.Co

end
end

section

noncomputable section

namespace GlobalTheory.LvT.Built.TrueLaws

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2

local instance starHost (B : Base) : StarRing B.host.E := B.fields.starE

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev dat (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) : Dat (I.rec7 l Z) u :=
  Inh.ofOk B (I.cols l) Z.W Z.V Z.S Z.N Z.G u (I.chIn u a) (I.atIn u a) (I.perIn u a) (I.fmIn l.pr u a) (l.ch u a) (l.lev u a)
    (l.per u a) (l.ovr u a)

instance datFE (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (Bd : Dat (I.rec7 l Z) u) : Field Bd.E := Bd.fE

instance datSE (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (Bd : Dat (I.rec7 l Z) u) : StarRing Bd.E := Bd.sE

theorem dat_ch (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    (dat I l Z u a).ch = tw (I.tw l l0 Z) u a := rfl

theorem own_eq (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    own (I.rec7 l Z) u = tw (I.tw l l0 Z) u I.mu0 := rfl

variable {I}

theorem isTerm (h : I.Ok) (u : B.Word) (a : I.ι) {i : ℕ} (hi : i < B.R.m) :
    KerIsTerm (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  exact IsTerm.kerIsTerm B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i hX hPr h.sel_ok
    (h.T_mem u) (h.idx_ok a) hi h.ch_ok h.g_mem ⟨_, _, _, _, h.ch_tied⟩ I.A

theorem kerDil (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) {i : ℕ} (hi : i < B.R.m) :
    Dat.KerDil (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  intro b b' d d' P c
  exact kAt_dia B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i hX hPr h.sel_ok (h.T_mem u)
    (h.idx_ok a) (I.Tp a) I.A (isTerm h u a hi) b b' d d' P c

theorem split (u : B.Word) (a : I.ι) (h : I.Ok) (i : ℕ) :
    Nonempty (Split ((I.atIn u a).A i) (B.T u)) := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨sp, -⟩ := SplitPts.exists_split B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i hX hPr
    h.sel_ok (h.T_mem u) (h.idx_ok a) (I.Tp a)
  exact ⟨⟨sp.off, sp.off_act, sp.off_lat, sp.ext, sp.surj, sp.off_up, sp.off_dn, sp.off_dia, sp.dia_deco, sp.gam_surj, sp.T_mem,
    sp.T_nsq, sp.nonconj⟩⟩

open Classical in
theorem sees (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) : (dat I l Z u a).Sees :=
  Inh.sees_ofOk B (I.cols l) Z.W Z.V Z.S Z.N Z.G u X (I.chIn u a) (I.atIn u a) (I.perIn u a) (I.fmIn l.pr u a) (l.ch u a)
    (l.lev u a) (l.per u a) (l.ovr u a) rfl (fun _ h => h) (fun _ _ => rfl) (fun _ => decide_eq_true_iff)

local instance moveStepDatNumberField (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) : @NumberField (dat I l Z u a).E (dat I l Z u a).fE :=
  (dat I l Z u a).nE

theorem kerEq (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (hth : _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)))
    {i : ℕ} (hi : i < B.R.m)
    (hk : ∀ c c' F, (dat I l Z u a).ch.C.Kmap i c c' ((dat I l Z u a).ev i F) = (dat I l Z u a).ev (i + 1)
      (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i c.1 c'.1 (((dat I l Z u a).I.S i).rep c)
        (((dat I l Z u a).I.S (i + 1)).rep c') F)) :
    Dat.KerEq (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  refine ⟨fun b b' g g' d d' => ?_, hk⟩
  rcases lt_trichotomy (i + 2) B.R.m with h1 | h1 | h1
  · exact MatLaw.kAt_equiv B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i I.A
      hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) hth h1 b b' g g' d d'
  · exact CoupledLaw.kAt_equiv B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i I.A
      hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) hth h1 b b' g g' d d'
  · exact TopEq.kAt_top_equiv B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i I.A
      hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) hth (by omega) b b' g g' d d'

end GlobalTheory.LvT.Built.TrueLaws
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem trueCols_exists_primitiveRoots : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : Fin 2), (∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i)) ∧ ∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i - 1) := by
  intro B X I h l Z i
  have hP := (base_fields_primes_ok B X).2.1
  have hf : 0 < B.fields.f := by
    have e : B.fields.f = 2 * B.R.ord := B.fields_f
    have := B.R.ord_pos
    rw [e]; omega
  exact colRoots_exists_primitiveRoots B.fields (B.primes X) B.R.m I.Ch hf hP h.ch_ok i

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ

theorem trueWeights_built : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (τ : B.fields.Tau), Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ = GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ ∧ Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ = (I.perIn u a).sgT τ ∧ Br.Interlace (N_m_succ B.R) (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u a).sgT τ) ∧ Br.SameShift (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u a).sgT τ) ∧ ((I.rec7 l Z).fm u).SgInterlace := by
  intro B X I _ l Z u a τ
  have hc : Formalism.MainNotions.product_first_zeroth_parts.cTw B.R = (B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ) := by
    have h2 : 2 ∣ B.R.t + 1 := B.R.t_odd.add_one.two_dvd
    unfold Formalism.MainNotions.product_first_zeroth_parts.cTw
    rw [Nat.mul_div_assoc _ h2]
    push_cast; rfl
  have key : ∀ {n : ℕ} (w : DomWeight n), Formalism.MainNotions.product_first_zeroth_parts.wSh w (Formalism.MainNotions.product_first_zeroth_parts.cTw B.R) =
      GlobalTheory.Mem.Col2.shW w (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))) := by
    intro n w
    unfold Formalism.MainNotions.product_first_zeroth_parts.wSh GlobalTheory.Mem.Col2.shW
    congr 1
    funext i
    rw [hc]; ring
  have hs : ∀ τ, (I.perIn u a).sg τ = (RowPar.of (B.hcW u τ)).sg := fun τ =>
    congrArg RowPar.sg (B.wts_isOk.hc_row u τ).symm
  have hw := GlobalTheory.LvT.BuiltChain.weights_ok (I.perIn u a) (B.hcW u) B.fields.emb hs
  refine ⟨key _, key _, (hw τ).1, (hw τ).2, fun τ' i => ?_⟩
  obtain ⟨ha, hb⟩ := (hw τ').1 i
  simp only [Br.aBr, Br.bBr, Br.iS, Br.iC, PerIn.sgT, GlobalTheory.Mem.Col2.lamT, GlobalTheory.Mem.Col2.shW] at ha hb
  constructor
  · show (B.wts.sgW τ').w i ≤ (Examples₂.lamOf (B.hcW u τ') B.R.m).w ⟨i.1, _⟩
    change 0 ≤ (Examples₂.lamOf (B.hcW u τ') B.R.m).w ⟨i.1, _⟩ + _ - ((B.wts.sgW τ').w i + _) at hb
    linarith
  · show (Examples₂.lamOf (B.hcW u τ') B.R.m).w ⟨i.1 + 1, _⟩ ≤ (B.wts.sgW τ').w i
    change 0 ≤ (B.wts.sgW τ').w i + _ - ((Examples₂.lamOf (B.hcW u τ') B.R.m).w ⟨i.1 + 1, _⟩ + _) at ha
    linarith

end GlobalTheory.PerQ
end

section

noncomputable section

namespace GlobalTheory.PairAtClass

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

section

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
  (emb : ι → E →+* K) (σ : K →+* ℂ) {R : Ranks} {I : ChainIn E K ι R} (Q : PerIn I) (hQ : Q.Ok)

theorem petersson_single_left (g w : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ) (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] :
    Q.ipP emb σ hQ (fun c' => if c' = c then g c' else 0) w = Q.wt c * ipVal emb σ Q.sgT (g c) (w c) := by
  letI := Q.clFin hQ
  simp only [PerIn.ipP, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine (Finset.sum_eq_single c (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ c) h)).trans ?_
  · simp [hb]
  · simp

theorem petersson_single_right (g w : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ) (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] :
    Q.ipP emb σ hQ g (fun c' => if c' = c then w c' else 0) = Q.wt c * ipVal emb σ Q.sgT (g c) (w c) := by
  letI := Q.clFin hQ
  simp only [PerIn.ipP, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine (Finset.sum_eq_single c (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ c) h)).trans ?_
  · simp [hb]
  · simp

theorem period_single (hI : I.Ok) (hc : ι → HCParam R) (G : Q.Mt emb σ)
    (w : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ) (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] :
    (Q.per emb σ hI hQ hc).period (fun c' => if c' = c then w c' else 0) G =
      Q.wt c * pairB Q.sgT (polOf (Gr emb σ (R.N R.m - 1)) (shiftOf Q.sgT) (fr0 emb σ (R.N R.m - 1)) (w c))
        (Q.rd emb σ G c) := by
  letI := Q.clFin hQ
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine (Finset.sum_eq_single c (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ c) h)).trans ?_
  · simp [hb]
  · simp

end

theorem pair_integral : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {R : Ranks} {I : ChainIn E K ι R} (Q : PerIn I) (hI : I.Ok) (hQ : Q.Ok) (hc : ι → HCParam R) (hF : (Q.S'.fam emb Q.sgT).Ok) (G : Q.Mt emb σ) (g : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ), (∀ w, (Q.per emb σ hI hQ hc).period w G = Q.ipP emb σ hQ g w) → ∀ (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] (y : Formalism.L2.DIV.VV K Q.sgT), y ∈ nabAt emb Q.sgT (Q.S'.Lsh c.1 (Q.S'.rep c)) → Q.rd emb σ G c = MvPolynomial.map σ y.1 → ∀ x ∈ (Q.S'.hlat emb Q.sgT hF).L, ∃ a : 𝓞 K, σ (a : K) = ((Nat.card (Q.S'.Stab c) : ℕ) : ℂ) * Q.ipP emb σ hQ (fun c' => if c' = c then g c' else 0) (fun c' => if c' = c then Q.S'.embF emb σ Q.sgT hF x c' else 0) := by
  intro E K ι _ _ _ _ _ _ _ emb σ R I Q hI hQ hc hF G g hP c _ y hy hG x hx
  have hfin := hQ.step.fin_stab c.1 (Q.S'.rep c)
  have hne : ((Nat.card (Q.S'.Stab c) : ℕ) : ℂ) ≠ 0 := by
    haveI := hfin
    exact_mod_cast Nat.card_pos.ne'
  have hint := ((GlobalTheory.PeriodClassSum.pairBDual E K ι _ emb Q.sgT _ (hQ.step.lsh_full_lat c.1 (Q.S'.rep c)) (x.1 c)).1.1
    (hx c)) y hy
  obtain ⟨a, ha⟩ := hint
  refine ⟨a, ?_⟩
  have e12 : Q.ipP emb σ hQ (fun c' => if c' = c then g c' else 0)
      (fun c' => if c' = c then Q.S'.embF emb σ Q.sgT hF x c' else 0) =
      Q.ipP emb σ hQ g (fun c' => if c' = c then Q.S'.embF emb σ Q.sgT hF x c' else 0) := by
    rw [petersson_single_left, petersson_single_right]
    simp
  rw [e12, ← hP, period_single, hG]
  show _ = _ * (Q.wt c * pairB Q.sgT (polOf (Gr emb σ (R.N R.m - 1)) (shiftOf Q.sgT) (fr0 emb σ (R.N R.m - 1))
    (evV emb (1 : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) E) Q.sgT σ (x.1 c))) (MvPolynomial.map σ y.1))
  rw [GlobalTheory.PeriodOnStep.polOf_evV, ← GlobalTheory.PeriodOnStep.map_pairB, ← pairBK_apply, PerIn.wt, ← mul_assoc,
    mul_inv_cancel₀ hne, one_mul]
  rw [← ha, LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_one]

end GlobalTheory.PairAtClass
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.ChiDet

theorem tildeQ_detPt_eq_chiId : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (e : Fin R.m → R.Psi → ℚ) (C : GlobalTheory.Mem.Chr.HFrame H e) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E))), letI := H.cmStar; ∀ (p : DecoF H.E n ST SG Q), LevOk H SG SQ → ((tildeQ H SQ C.chiPsi (detPt H SQ p) : ℂˣ) : ℂ) = chiId C.chiPsi (Th.detId H (Th.stdL H n) p.deco.1.N) := by
  intro R H e C n ST SG Q SQ
  letI := H.cmStar
  intro p hL
  have hχ := C.isChi
  have hK := (GlobalTheory.Mem.KerDet.kernel_open_and_factor R H).2.2.2 C.chiPsi hχ.triv (fun v y hy _ => hχ.unr v y hy)
    fun v _ => hχ.unr v
  rw [tildeQ_eq_comp H SQ hK, MonoidHom.comp_apply]
  exact tildeD_eq_chiId R H C.chiPsi hχ n _ p.deco.2.lat _
    (congrArg (toDtTMod H SQ) (mk_detPt_eq_relDetQ R H n ST SG Q SQ p hL))

end GlobalTheory.Mem.ChiDet
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

theorem _root_.GlobalTheory.T.tame_character_values_eq_heckeChar_local_values : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (K : Type) [Field K] (σ : K →+* ℂ) (μ : Chr F E K) (ξ : Formalism.L2.Host.HChar E), GlobalTheory.Mem.Col2.Reads σ μ ξ → (∀ P, ξ.TameAt P) → ∀ P : HeightOneSpectrum (𝓞 E), (ξ.UnrAt P → σ ((unifVal μ P : Kˣ) : K) = ((ξ.val P : ℂˣ) : ℂ)) ∧ (((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ q : Eˣ, (q : E) = ((Ideal.absNorm P.asIdeal : ℕ) : E) → σ ((qVal μ P : Kˣ) : K) = ((ξ.locK P q : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.TwistVal.main | exact GlobalTheory.TwistVal.main | (intros; apply GlobalTheory.TwistVal.main <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

theorem _root_.GlobalTheory.T.compactSpace_definiteUnitaryInfinitePoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), CompactSpace (infU E n) := by
  first | exact @GlobalTheory.InfUCompact.compactSpace_infU | exact GlobalTheory.InfUCompact.compactSpace_infU | (intros; apply GlobalTheory.InfUCompact.compactSpace_infU <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitianClassNumberItems_all_ranks : ∀ (D : D7) (n : ℕ), ClassItemsAt D n := by
  first | exact @GlobalTheory.classItemsAt_all | exact GlobalTheory.classItemsAt_all | (intros; apply GlobalTheory.classItemsAt_all <;> assumption)
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomEq

theorem eq_and_alg : (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ) ∧ (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ t : VC D N N', (∃ a : ℕ, 0 < a ∧ a • t ∈ La D B.tor L L') → ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (U D B.tor t (B.eNat χ N N' L L')) α ∈ Qbar) :=
  ⟨fun _ _ _ B χ hcc hδ hχ => Formalism.L2.PairingIndexBounds.Eq.SqG.eulerProduct_eq_of_curve_ideal B hcc hδ χ hχ,
   fun D cc δ B χ hcc hδ hχ => GlobalTheory.ThLoc.algTAll D cc δ B χ hcc hδ hχ⟩

end GlobalTheory.MomEq
end
