module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle010
public import Formalism.UnipotentAdelicQuotients.Bundle003
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle293
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle159
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle418
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle266
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle308
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle537
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle140
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle445
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle328
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle239
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle395
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle146
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle363
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle341
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepAverageKillsThetaOfDenseFamily
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EvaluationFormAbsoluteConvergence
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatPeriodEqIntegralEvaluationPeriods
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle538
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.corankOnePairsFamilyBounds_of_siegelWeil : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} true ∧ GlobalTheory.Core.Diag.OneOn {c} false := by
  first | exact @GlobalTheory.Core.Diag.oneOn_singleton_of_siegelWeil | exact GlobalTheory.Core.Diag.oneOn_singleton_of_siegelWeil | (intros; apply GlobalTheory.Core.Diag.oneOn_singleton_of_siegelWeil <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms NumberField Matrix GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.AdForm ValuativeRel IsLocalRing

theorem _root_.GlobalTheory.T.levelPrimeOperators_act_ramifiedColumns_vanishing : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ιc : ∀ j, Ch j → Ch₀ j), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, GlobalTheory.FinPl.Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)) (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)), StdT I l Z u p β Q L → ∀ (J : List ι) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1), ∃ S : ∀ j, (ι → 𝓀[k]ˣ) → ColT I l u a j → ColT I l u a j, ∀ j (hj : j ≤ B.R.m) φ, A.RamL ιc j φ → (∀ b y, IsContAut _ (A.rd θ j hj b φ y) ∧ ∀ i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (A.rd θ j hj b φ y)) ∧ ∀ η, A.RamL ιc j (S j η φ) ∧ ∀ b y, A.rd θ j hj b (S j η φ) y = J.foldr (fun i f => sOp (β j i) (Q j i) q (resChar (χ i) (hχ i) q) (η i) f) (A.rd θ j hj b φ y) := by
  first | exact @GlobalTheory.AdForm.twS_ramL | exact GlobalTheory.AdForm.twS_ramL | (intros; apply GlobalTheory.AdForm.twS_ramL <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerTup

theorem jetP_cast (D : D7) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (s : ℂ) (cD : D.what₂.Tau → ℂ)
    (hcD : ∀ τ, cD τ ≠ 0) (G : VCx D.what₂.Tau a b → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    jetP S T hS hT s G P = jetL cD G (mvZ (fun _ => 1) (fun τ => (s / cD τ) • 1) (castP hS hT P)) := by
  subst hS hT
  have h1 : castP (D := D) (rfl : S.rank = S.rank) (rfl : T.rank = T.rank) P = P := by
    conv_rhs => rw [← MvPolynomial.rename_id_apply P]
    rfl
  rw [h1]
  exact GlobalTheory.T.fockPolynomialJetValue_eq_jetLinearForm_rescaled D S T s cD hcD G P

theorem jetC_zero {ι : Type} [Fintype ι] {a b : ℕ} (cD : ι → ℂ) (m : Formalism.L2.Ker.DVar ι a b →₀ ℕ) :
    jetC cD (fun _ : VCx ι a b => (0 : ℂ)) m = 0 := by
  change jetC cD (0 : VCx ι a b → ℂ) m = 0
  simp only [jetC, derivAt0, iteratedFDeriv_zero, Pi.zero_apply, zero_apply, mul_zero]

theorem jetP_zero (D : D7) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (s : ℂ)
    (P : MvPolynomial (FVar D T.rank S.rank) ℂ) : jetP S T hS hT s (fun _ => 0) P = 0 := by
  simp only [jetP, jetC_zero, mul_zero, Finset.sum_const_zero]

theorem jetL_zero {ι : Type} [Fintype ι] {a b : ℕ} (cD : ι → ℂ) : jetL cD (fun _ : VCx ι a b => (0 : ℂ)) = 0 := by
  have h : (fun m => jetC cD (fun _ : VCx ι a b => (0 : ℂ)) m) = 0 := funext fun m => jetC_zero cD m
  simp only [jetL, h, map_zero]

theorem toHom_surj {D : D7} (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b)
    (y : (Fin a → D.host.E) →ₗ[D.host.E] Fin b → D.host.E) : ∃ z, toHom S T hS hT z = y :=
  ⟨(Matrix.reindex (finCongr hT) (finCongr hS)).symm (LinearMap.toMatrix' y), by
    unfold toHom
    rw [Equiv.apply_symm_apply, Matrix.toLin'_toMatrix']⟩

theorem supp_per_of_inBox {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}
    (SS : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ) (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a))
    (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (Ξ : Formalism.L2.Col.HomE E a b → K)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.InBox SS cA cB N N' Ξ) (f : K →+* ℂ) (p : ℂ) :
    (∀ y, p * f (Ξ y) ≠ 0 → ((cA * cB : ℕ) : E) • y ∈ Formalism.L2.Col.homAt SS N N') ∧
    (∀ y, ∀ z ∈ Formalism.L2.Col.homAt SS N N', p * f (Ξ (y + ((cA * cB : ℕ) : E) • z)) = p * f (Ξ y)) := by
  have key : ∀ (n : ℕ) (y : Formalism.L2.Col.HomE E a b), ((n : E) • y) = ((n : 𝓞 E) • y) := fun n y => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  refine ⟨fun y hy => ?_, fun y z hz => ?_⟩
  · have hx : Ξ y ≠ 0 := fun h0 => hy (by rw [h0, map_zero, mul_zero])
    have h1 := hB.1 y hx
    rw [Formalism.L2.Col.divLat, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] at h1
    rw [key, Nat.cast_mul, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ h1
  · have hz' : ((cA * cB : ℕ) : E) • z ∈ Formalism.L2.Col.mulLat cB (Formalism.L2.Col.homAt SS N N') := by
      rw [key, Nat.cast_mul, mul_comm, mul_smul]
      exact Submodule.mem_map.2 ⟨_, Submodule.smul_mem _ _ hz, rfl⟩
    rw [hB.2 y _ hz']

theorem jetP_zero' (D : D7) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (s : ℂ)
    (P : MvPolynomial (FVar D T.rank S.rank) ℂ) : jetP S T hS hT s (0 : VCx D.what₂.Tau a b → ℂ) P = 0 :=
  jetP_zero D S T hS hT s P

theorem jetL_zero' {ι : Type} [Fintype ι] {a b : ℕ} (cD : ι → ℂ) : jetL cD (0 : VCx ι a b → ℂ) = 0 := jetL_zero cD

end GlobalTheory.KerTup




open GlobalTheory.KerTup in
theorem GlobalTheory.KerTup.kernel_identity_tuple : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) ψ θ x vac c₀ kom dd w Ram rd cK, PinX I l Z ψ θ x vac c₀ → PinColL A ι ψ θ x vac c₀ kom dd w Ram rd cK → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (s : ℂ), (∀ f, IsHol θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) ψ f → ∀ P, pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 = jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s (ColDat.xiS θ i hi f) P) → ∀ α γ (c : {c // A.chOf i c = ι i α}) (c' : {c // A.chOf (i + 1) c = ι (i + 1) γ}) P, (volLev (x i).vol (A.U i (ι i α)) : ℂ) * thetaKO (kom i) (A.h i _ c) (A.h (i + 1) _ c') (pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (comb ψ _ _ (dd i α γ) (vac i)) P) = cK i * A.abelian₂ i c.1 c'.1 (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) := by
  intro B X I hI hP l Z u a Ch₀ Ch A ι ψ θ x vac c₀ kom dd w Ram rd cK hX hC i hi s hHol α γ c c' P
  obtain ⟨hStd, hGram, hEmb, hcD, hDet⟩ := GlobalTheory.T.trueColumnSteps_are_standardHermitianPairs I hI hP l Z ψ θ hX.std hX.inf
  obtain ⟨hFin, Φ, hSB, hΦv, hTh⟩ := hC.dat i hi α γ
  obtain ⟨hMv, hMv', hΞ⟩ := GlobalTheory.T.movedDatum_eq_finiteDatum_representativePair I hI hP l Z u a Ch₀ A hC.is i hi (ι i α) (ι (i + 1) γ) Φ hSB (w i α γ) hΦv c c'
  obtain ⟨xg, hxg⟩ := hDet _ (A.h i (ι i α) c)
  obtain ⟨yh, hyh⟩ := hDet _ (A.h (i + 1) (ι (i + 1) γ) c')
  have hV := (hX.mv i hi).2 a (A.chr (i + 1)) (kom i) (hC.is.chr ⟨i, hi⟩) (hC.om i hi) (A.h i _ c)
    (hC.is.h i (Nat.le_of_succ_le hi) _ c).1 (A.h (i + 1) _ c') (hC.is.h (i + 1) hi _ c').1 _ _ hMv hMv' xg yh hxg hyh
  have hχ := GlobalTheory.T.chainMove_characters_eq_rho_up_to_base I hI hP l Z u a Ch₀ A hC.is i hi _ _ c c' xg yh hxg hyh
  obtain ⟨hc0, hcov, h2qd⟩ := GlobalTheory.T.tupleLevel_pos_odd_badPrimes_prime_to_level I hI hP u a
  obtain ⟨hXo, hPr, -⟩ := base_fields_primes_ok B X
  have hi' : i < B.R.m := hi
  have hbox := GlobalTheory.LvT.Built.Box.inBox_xiAt B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) _ _ u i hXo hPr
    hI.sel_ok (hI.T_mem u) hI.g_mem (hI.idx_ok a) hi' ⟨_, _, _, _, hI.ch_tied⟩ c.1.1 c'.1.1 ((I.stp u a i).rep c.1)
    ((I.stp u a (i + 1)).rep c'.1)
  have hLH := (TC.laHyp_eSmooth_true I hI hP l Z a u i hi').1
  have hLa := (hLH.2.2.2.2.2 _ _ ⟨((I.stp u a i).rep c.1).1.1.deco.2.lat, ((I.stp u a i).rep c.1).1.1.deco.2.uni⟩
    ⟨((I.stp u a (i + 1)).rep c'.1).1.1.deco.2.lat, ((I.stp u a (i + 1)).rep c'.1).1.1.deco.2.uni⟩).2
  have he : B.fields.embC I.A.σ₀ = tauE (I.rec7 l Z) := funext hEmb
  rw [he, ColIn.A_AA] at hLa
  set N := ((I.stp u a i).rep c.1).1.1.deco.1.N with hN
  set N' := ((I.stp u a (i + 1)).rep c'.1).1.1.deco.1.N with hN'
  have hΞ' : ∀ z, Φ (actO _ _ (A.h i _ c)⁻¹ (A.h (i + 1) _ c')⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) =
      w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1)
        ((I.stp u a (i + 1)).rep c'.1) (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) z)) :=
    fun z => hΞ z
  obtain ⟨hsupp, hper⟩ := supp_per_of_inBox _ _ _ _ _ _ hbox B.embLL (w i α γ)
  have hth : I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) =
      thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E)
        (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1
          ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) (I.A.e _ _ N N') := by
    rw [← he]
    have h2 : ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) = I.A.AA := (ColIn.A_AA I).symm
    rw [h2]
    rfl
  have hcore := fun (κ : ℂ) (E : VCx (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1)) → ℂ) => GlobalTheory.T.thetaKernel_splitPlaces_eq_jet_classicalTheta (I.rec7 l Z) ψ θ _ _ (B.R.N i) (B.R.N (i + 1)) (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi))
    (rankN (I.rec7 l Z) (i + 1) hi) I.A.δ I.A.sc (hStd i hi) s hHol (A.chr (i + 1)) (kom i) (hC.om i hi) A.e (ColIn.Sb I a u)
    hC.is.idem (vac i) Φ (comb ψ _ _ (dd i α γ) (vac i)) (hX.vc i hi) hSB hTh (A.h i _ c) (hC.is.h i (Nat.le_of_succ_le hi) _ c).1
    (A.h (i + 1) _ c') (hC.is.h (i + 1) hi _ c').1 N N' hMv hMv' (levC I.sel (I.tup a) (I.cst a) u) hc0 hcov h2qd hLa
    (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) hΞ' hsupp hper κ E
  have hjet := fun G => jetP_cast (I.rec7 l Z) _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s
    I.J.cD hcD G P
  have hxi0 : (∀ z, A.xi i hi (ι i α) (ι (i + 1) γ) z = 0) →
      ∀ y : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)), B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y) = 0 := by
    intro hz y
    obtain ⟨z, rfl⟩ := toHom_surj _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) y
    have h0 := (GlobalTheory.T.movedDatum_eq_finiteDatum_representativePair I hI hP l Z u a Ch₀ A hC.is i hi (ι i α) (ι (i + 1) γ) Φ hSB 0
      (fun z' => by simp only [hΦv z', hz z', mul_zero]) c c').2.2 z
    have h1 := (GlobalTheory.T.movedDatum_eq_finiteDatum_representativePair I hI hP l Z u a Ch₀ A hC.is i hi (ι i α) (ι (i + 1) γ) Φ hSB 1
      (fun z' => by simp only [hΦv z', hz z', mul_zero]) c c').2.2 z
    rw [h0, zero_mul, one_mul] at h1
    exact h1.symm
  by_cases hm : w i α γ ≠ 0 ∧ ∃ z, A.xi i hi (ι i α) (ι (i + 1) γ) z ≠ 0
  · obtain ⟨hw, hxz⟩ := hm
    have hVE : xiN θ _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) I.A.δ I.A.sc
        (kom i (A.h i _ c, A.h (i + 1) _ c') (vac i)) = fun z => (c₀ i * (A.chr (i + 1) (A.xr i (ι i α)) : ℂ) *
          (A.chr (i + 1) (A.xr (i + 1) (ι (i + 1) γ)) : ℂ)⁻¹ * ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) * w i α γ) *
          ((w i α γ)⁻¹ * I.A.e _ _ N N' z) := by
      refine hV.trans (funext fun z => ?_)
      have h3 : I.A.e _ _ N N' z = I.A.chiF _ _ N N' * I.J.V.thMoved _ _ N N' z := rfl
      rw [h3, mul_assoc (c₀ i), hχ]
      field_simp
    have hwE : (fun z => w i α γ * ((w i α γ)⁻¹ * I.A.e _ _ N N' z)) = I.A.e _ _ N N' :=
      funext fun z => by rw [← mul_assoc, mul_inv_cancel₀ hw, one_mul]
    have hT : jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s
        (thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E)
          (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) (fun z => (w i α γ)⁻¹ * I.A.e _ _ N N' z)) P =
        jetL I.J.cD (I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1))
          (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) := by
      have h6 : thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) (fun z => (w i α γ)⁻¹ * I.A.e _ _ N N' z) =
          I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) :=
        (GlobalTheory.T.classicalThetaOfDatum_smul_move _ _ _ _ _ _ _ _ _ _ _ _).trans ((congrArg (fun G => thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) G) hwE).trans hth.symm)
      exact (congrArg (fun t => jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s t P) h6).trans (hjet _)
    rw [hcore _ _ hVE, hC.cst i hi α γ hxz]
    refine (congrArg (fun t => _ * (_ * t)) hT).trans ?_
    have hT'' : jetL I.J.cD (I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1))
          (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) * ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) = A.abelian₂ i c.1 c'.1 (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) := mul_comm _ _
    refine Eq.trans ?_ (congrArg (fun t => _ * t) hT'')
    ring
  · have hΞz : (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) = fun _ => 0 := by
      funext y
      by_cases hw : w i α γ = 0
      · rw [hw, zero_mul]
      · have hz : ∀ z, A.xi i hi (ι i α) (ι (i + 1) γ) z = 0 := fun z => by_contra fun h => hm ⟨hw, z, h⟩
        rw [hxi0 hz y, mul_zero]
    have hT0 : jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s
        (thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E)
          (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) (I.J.V.thMoved _ _ N N')) P = 0 := by
      have h5 : thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) (I.J.V.thMoved _ _ N N') = 0 :=
        (congrArg (fun G : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)) → ℂ => thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) G (I.J.V.thMoved _ _ N N')) hΞz).trans (thC_zero _ _ _ _ _ _ _ _ _ _)
      exact (congrArg (fun t => jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s t P) h5).trans (jetP_zero' _ _ _ _ _ s P)
    rw [hcore _ _ hV]
    refine (congrArg (fun t => _ * (_ * t)) hT0).trans ?_
    simp only [mul_zero]
    by_cases hxz : ∃ z, A.xi i hi (ι i α) (ι (i + 1) γ) z ≠ 0
    · have hw : w i α γ = 0 := by
        by_contra hw
        exact hm ⟨hw, hxz⟩
      rw [hC.cst i hi α γ hxz, hw]
      simp
    · have hz : ∀ z, A.xi i hi (ι i α) (ι (i + 1) γ) z = 0 := fun z => by_contra fun h => hxz ⟨z, h⟩
      have hth0 : I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) = 0 := by
        rw [hth]
        have h4 : (fun y => B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) = fun _ => 0 := funext (hxi0 hz)
        exact (congrArg (fun G : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)) → ℂ => thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) G (I.A.e _ _ N N')) h4).trans (thC_zero _ _ _ _ _ _ _ _ _ _)
      have hL0 : A.abelian₂ i c.1 c'.1 (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) = 0 := by
        show ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) • jetL I.J.cD (I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1))
          (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) = 0
        rw [hth0, jetL_zero', LinearMap.zero_apply, smul_zero]
      exact ((congrArg (fun t => cK i * t) hL0).trans (mul_zero _)).symm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.LevLaw

theorem latFr_stdLat (D : D7) (S : HSp D) (a : ℕ) (hS : S.rank = a) :
    latFr S hS (Formalism.L2.Col.stdLat D.host.E a) = intVec D S.rank := by
  subst hS
  rw [GlobalTheory.LatPairMove.latFr_rfl, coe_colStdLat]

theorem mem_stdHom_iff_actO (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (k : GA D S) (k' : GA D T)
    (h1 : Moves S hS 1 (Formalism.L2.Col.stdLat D.host.E a)) (h1' : Moves T hT 1 (Formalism.L2.Col.stdLat D.host.E b))
    (hk : Moves S hS k (Formalism.L2.Col.stdLat D.host.E a)) (hk' : Moves T hT k' (Formalism.L2.Col.stdLat D.host.E b)) :
    ∀ x, x ∈ stdHom S T ↔ actO S T k k' x ∈ stdHom S T := by
  have key := GlobalTheory.LatPairMove.latO_move D S T a b hS hT 1 k 1 k' _ _ _ _ h1 h1' (by rwa [mul_one]) (by rwa [mul_one])
  rw [latFr_stdLat, latFr_stdLat] at key
  intro x
  constructor
  · intro hx
    exact (key _).2 ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨u₀, hu₀, he⟩ := (key _).1 hx
    have hinv : ∀ v, actO S T k⁻¹ k'⁻¹ (actO S T k k' v) = v := fun v => by
      have := GlobalTheory.AdelicLatMove.actO_actO_inv S T k⁻¹ k'⁻¹ v
      rwa [inv_inv, inv_inv] at this
    have := congrArg (actO S T k⁻¹ k'⁻¹) he
    rw [hinv, hinv] at this
    rw [this]
    exact hu₀

theorem lev_law : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) ψ θ x vac c₀ kom dd w Ram rd cK, PinX I l Z ψ θ x vac c₀ → PinColL A ι ψ θ x vac c₀ kom dd w Ram rd cK → ∀ j, j < B.R.m → ∀ α γ (κ : A.U j (ι j α)) (κ' : A.U (j + 1) (ι (j + 1) γ)), kom j (κ.1, κ'.1) (comb ψ _ _ (dd j α γ) (vac j)) = (((A.chi j _ κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) _ κ' : ℂˣ) : ℂ)) • comb ψ _ _ (dd j α γ) (vac j) := by
  intro B X I hI hP l Z u a Ch₀ Ch A ι ψ θ x vac c₀ kom dd w Ram rd cK hX hC j hj α γ κ κ'
  have hj1 : j + 1 ≤ B.R.m := hj
  have hstd := GlobalTheory.T.trueColumnSteps_are_standardHermitianPairs I hI hP l Z ψ θ hX.std hX.inf
  have hSP := hstd.1 j hj1
  obtain ⟨xr, hxr⟩ := hstd.2.2.2.2 _ κ.1
  obtain ⟨yr, hyr⟩ := hstd.2.2.2.2 _ κ'.1
  have hU := hC.is.U j (Nat.le_of_succ_le hj1) (ι j α)
  have hU' := hC.is.U (j + 1) hj1 (ι (j + 1) γ)
  have hkG : κ.1 ∈ GfC _ := ((hU κ.1).1 κ.2).1
  have hkG' : κ'.1 ∈ GfC _ := ((hU' κ'.1).1 κ'.2).1
  have h1G : (1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) ∈ GfC _ := ((hU 1).1 (one_mem _)).1
  have h1G' : (1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (j + 1))) ∈ GfC _ := ((hU' 1).1 (one_mem _)).1
  have hMk := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is j (Nat.le_of_succ_le hj1) (ι j α) κ.1 κ.2
  have hMk' := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is (j + 1) hj1 (ι (j + 1) γ) κ'.1 κ'.2
  have hM1 := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is j (Nat.le_of_succ_le hj1) (ι j α) 1 (one_mem _)
  have hM1' := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is (j + 1) hj1 (ι (j + 1) γ) 1 (one_mem _)
  have hom := hC.om j hj
  have hVT := (hX.mv j hj1).2 a (A.chr (j + 1)) (kom j) (hC.is.chr ⟨j, hj⟩) hom
  have e1 := hVT κ.1 hkG κ'.1 hkG' _ _ hMk hMk' xr yr hxr hyr
  have e0 := hVT 1 h1G 1 h1G' _ _ hM1 hM1' 1 1 (GlobalTheory.SmallFix.isDetRoot_one _) (GlobalTheory.SmallFix.isDetRoot_one _)
  have h11 : kom j ((1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), (1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (j + 1)))) = 1 :=
    map_one (kom j)
  set p : ℂ := ((A.chr (j + 1) xr : ℂ))⁻¹ * (A.chr (j + 1) yr : ℂ) with hpdef
  have hvth : IsThetaFunO ψ _ _ (vac j) := (hX.vc j hj).2.theta
  have hp : kom j (κ.1, κ'.1) (vac j) = p • vac j := by
    have hf : IsThetaFunO ψ _ _ (kom j (κ.1, κ'.1) (vac j) - p • vac j) :=
      GlobalTheory.AvgKill.theta_sub' (hom.om_pres _ _ hvth) (GlobalTheory.LocMod.LinSpace.isThetaFunO_smul p hvth)
    have hz : xiN θ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj1)) (rankN (I.rec7 l Z) (j + 1) hj1) I.A.δ I.A.sc
        (kom j (κ.1, κ'.1) (vac j) - p • vac j) = 0 := by
      funext z
      have a1 := congrFun e1 z
      have a0 := congrFun e0 z
      rw [h11] at a0
      simp only [ColDat.xiS, xiN, Module.End.one_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, map_one, Circle.coe_one, inv_one, mul_one] at a1 a0 ⊢
      rw [hpdef, mul_sub, show ∀ q r s : ℂ, q * (r * s) = r * (q * s) from fun q r s => by ring]
      erw [a1, a0]
      ring
    exact sub_eq_zero.1 ((GlobalTheory.T.gaussianTwistedRealReading_entire_and_injective _ ψ θ _ _ _ _ _ _ _ _ hSP).2 _ hf hz)
  obtain ⟨-, Φ, hΦ, hΞ, hth⟩ := hC.dat j hj1 α γ
  have hq : ∀ z, IsHalf A.e z → p * Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z) =
      (((A.chi j _ κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) _ κ' : ℂˣ) : ℂ)) * Φ z := fun z hz =>
    GlobalTheory.T.finite_datum_law_under_two_chart_levels I hI hP l Z u a Ch₀ A hC.is j hj1 (ι j α) (ι (j + 1) γ) Φ hΦ (w j α γ) (fun z => hΞ z) κ κ' xr yr hxr hyr z hz
  have hlat := mem_stdHom_iff_actO (I.rec7 l Z) _ _ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj1))
    (rankN (I.rec7 l Z) (j + 1) hj1) κ.1 κ'.1 hM1 hM1' hMk hMk'
  exact GlobalTheory.T.weilAction_eq_smul_of_keeps_lattice (I.rec7 l Z) ψ θ _ _ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj1)) (rankN (I.rec7 l Z) (j + 1) hj1)
    I.A.δ I.A.sc hSP (A.chr (j + 1)) (kom j) hom A.e _ hC.is.idem (vac j) Φ _ (hX.vc j hj) hΦ hth κ.1 hkG κ'.1 hkG' hlat p _ hp hq

end GlobalTheory.AdForm.LevLaw
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChain_realZeta_nonvanishing : GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D → GlobalTheory.ChainOnto.RealZeta D := by
  first | exact @GlobalTheory.RealZetaProof.realZeta | exact GlobalTheory.RealZetaProof.realZeta | (intros; apply GlobalTheory.RealZetaProof.realZeta <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.twistedChain_realZeta_nonvanishing : GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D → RealZetaQ D := by
  first | exact @GlobalTheory.RealZetaTw.realZetaTw | exact GlobalTheory.RealZetaTw.realZetaTw | (intros; apply GlobalTheory.RealZetaTw.realZetaTw <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.evaluationForm_absolute_convergence : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → ∃ z', IsQuotIntL1 J.μR s.vW.μ (fun h => ((∫ u : UX D ρ, ‖J.perAll ψ B s.om₀ φ (rTrans (J.d.levi u.1 * h) G) (evalBF s (s.om (1, (J.d.levi u.1 * h)) Φ))‖ ∂s.vU.ν : ℝ) : ℂ)) z' := by
  first | exact @GlobalTheory.Unf.evalBF_abs | exact GlobalTheory.Unf.evalBF_abs | (intros; apply GlobalTheory.Unf.evalBF_abs <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.flatPeriod_eq_integral_evaluationPeriods : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → ∀ h, Integrable (fun u : UX D ρ => J.perAll ψ B s.om₀ φ (rTrans (J.d.levi u.1 * h) G) (evalBF s (s.om (1, (J.d.levi u.1 * h)) Φ))) s.vU.ν ∧ J.perAll ψ B s.om₀ φ (rTrans h G) (flatBF s (s.om (1, h) Φ)) = ∫ u : UX D ρ, J.perAll ψ B s.om₀ φ (rTrans (J.d.levi u.1 * h) G) (evalBF s (s.om (1, (J.d.levi u.1 * h)) Φ)) ∂s.vU.ν := by
  first | exact @GlobalTheory.FlatEval.perAll_flat_eq_integral | exact GlobalTheory.FlatEval.perAll_flat_eq_integral | (intros; apply GlobalTheory.FlatEval.perAll_flat_eq_integral <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.thetaKernel_mean_eq_orbit_sum_mean : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ Ψ : WO V W → ℂ, IsThetaFunO ψ V W Ψ → ∫ n in vN.𝓝, Th n.1 * om (n.1, 1) Ψ 0 ∂vN.ν = ∫ n in vN.𝓝, ∑' x : Orb W x₀, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν := by
  first | exact @GlobalTheory.Unf.mean_theta_orbit | exact GlobalTheory.Unf.mean_theta_orbit | (intros; apply GlobalTheory.Unf.mean_theta_orbit <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

theorem _root_.GlobalTheory.T.unfoldedFunction_eq_besselPeriodIntegrand : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V Φ → ∀ (h : GA D B.V) (h₁ : GA D B.A) (n : flagN B.d), unfF s vL Y G Φ (n.1 * embA B.d B.o h₁ * h) = besFun ψ 1 B.d B.o B.ζ (handFB s vL Y (flatFB s (s.om (1, h) Φ))) (rTrans h G) h₁ n := by
  first | exact @GlobalTheory.Unf.FB.BesselIntegrand.unfF_eq_besFun | exact GlobalTheory.Unf.FB.BesselIntegrand.unfF_eq_besFun | (intros; apply GlobalTheory.Unf.FB.BesselIntegrand.unfF_eq_besFun <;> assumption)
end
