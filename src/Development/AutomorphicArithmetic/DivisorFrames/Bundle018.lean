module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1365
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle332
public import Development.AutomorphicArithmetic.LocalEmbeddings.ComplEquivEvW
public import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsIsSBHalfThetaOfSelfDualLattices
public import Development.AutomorphicArithmetic.DivisorFrames.IdempotentSumFixesIffHalfEl
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle010
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle005
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle017
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle015
public import Development.AutomorphicArithmetic.DivisorFrames.HasWeightAtOfNeZeroIntertwining
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle016
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle003
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.LocalEmbeddings.StageGeoDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem piW_cA' {D : D7} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : AE D) :
    piW t (cA D w) = piW (t.comp D.sp.cm.sig) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem piW_incA' {D : D7} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (e : D.host.E) : piW t (incA D e) = t e := by
  change GlobalTheory.AdelicU.evFin D.host.F v 1 * t e = t e
  simp

private theorem coord_eq {D : D7} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (A' WW : HSp D) {d : ℕ} (e : Fin d ≃ Fin WW.rank)
    (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (y : WO A' WW) :
    (βA'⁻¹).1.map (evW t) * (ptO A'.gram e y).map (piW (t.comp D.sp.cm.sig)) *
        ((D.host.xi0 • (WW.gramᵀ).submatrix e e).map t)ᵀ * (βW.1.map (evW t)).submatrix e e =
      ((GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y).map (evW t)).submatrix id e := by
  have hG : (A'.gram⁻¹)ᴴ = A'.gram⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv]
    congr 1
    refine Matrix.ext fun i j => ?_
    exact GlobalTheory.DualPairCheck.gram_star A' j i
  have h0 : ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (A'.gram⁻¹))ᵀ).map (piW (t.comp D.sp.cm.sig)) = (A'.gram⁻¹).map t := by
    refine Matrix.ext fun i j => ?_
    have h := congrFun (congrFun hG i) j
    change piW (t.comp D.sp.cm.sig) (incA D (A'.gram⁻¹ j i)) = t (A'.gram⁻¹ i j)
    rw [piW_incA', ← h]
    rfl
  have h2 : (ptO A'.gram e y).map (piW (t.comp D.sp.cm.sig)) =
      ((A'.gram⁻¹).map t * ((y : Matrix _ _ (AE D))ᵀ).map (piW (t.comp D.sp.cm.sig))).submatrix id e := by
    rw [← h0, ← Matrix.map_mul, ← Matrix.transpose_mul]
    rfl
  have h3 : ((D.host.xi0 • (WW.gramᵀ).submatrix e e).map t)ᵀ = t D.host.xi0 • (WW.gram.map t).submatrix e e := by
    refine Matrix.ext fun i j => ?_
    simp
  have hinc : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) D.host.E),
      ((M.map (incA D)).map (toEAf D)).map (evW t) = M.map t := by
    intro p q M
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, GlobalTheory.BotMatch.evW_toEAf, piW_incA']
  have hy : ((((y : Matrix _ _ (AE D)).map (cA D))ᵀ).map (toEAf D)).map (evW t) =
      ((y : Matrix _ _ (AE D))ᵀ).map (piW (t.comp D.sp.cm.sig)) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.transpose_apply, GlobalTheory.BotMatch.evW_toEAf, piW_cA']
  have hxi : evW t (eToEAf D D.host.xi0) = t D.host.xi0 := by
    rw [← piW_incA' t, ← GlobalTheory.BotMatch.evW_toEAf]
    rfl
  have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y).map (evW t) =
      t D.host.xi0 • ((βA'⁻¹).1.map (evW t) * ((A'.gram⁻¹).map t *
        ((y : Matrix _ _ (AE D))ᵀ).map (piW (t.comp D.sp.cm.sig)) * WW.gram.map t) * βW.1.map (evW t)) := by
    rw [← hxi, ← hinc, ← hinc, ← hy, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul,
      ← Matrix.map_mul, ← Matrix.map_mul]
    refine Matrix.ext fun i j => ?_
    exact map_mul (evW t) _ _
  rw [h1, h2, h3, Matrix.mul_smul, Matrix.smul_mul, Matrix.submatrix_smul]
  simp only [Pi.smul_apply]
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.mul_assoc]
  rfl

theorem UpperTheory.triple_dualCoord_split_places_of_isPair_isLat :
    ∀ (D : D7) (T : Type) (A A' WW : HSp D) (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
        (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))),
        X.Is ψ θ α β νH S → ∀ (hr : A.rank + A'.rank = WW.rank) (Bs : Base D.host.F D.host.E)
        (Vs : Spc D.host.F D.host.E A'.rank) (Ws : Spc D.host.F D.host.E (A.rank + A'.rank)) (M : Model D.sp.cm.sig Vs Ws),
        IsPair ψ false A' WW (finCongr hr) Bs Vs Ws M → IsLat (finCongr hr) Vs Ws X.rA'.Λ X.rW.Λ →
        ∀ (t : T) (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (τ : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v),
        (∀ w, w ∈ S t ↔ ∃ v : P, splitPrime (τ v) = w) →
        ∀ (b : ∀ v : P, GL (Fin A'.rank) (Fv D.host.F v)) (c : ∀ v : P, GL (Fin (A.rank + A'.rank)) (Fv D.host.F v))
          (ι : ∀ v : P, ((Fin A'.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ) →ₗ[ℂ]
            (Matrix (Fin A'.rank) (Fin (A.rank + A'.rank)) (Fv D.host.F v) → ℂ)),
        (∀ v, ((b v)⁻¹).1 = (A'.gram.map (τ v) * X.rA'.β.1.map (evW (τ v)))ᵀ) →
        (∀ v, (c v).1 = (X.rW.β.1.map (evW (τ v))).submatrix (finCongr hr) (finCongr hr)) →
        (∀ v, M.IsLinBar ψ (τ v) (b v) (c v) (ι v)) → (∀ v : P, ι v (M.vac v) 0 = 1) →
        ∀ (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin A'.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ v, v ∉ P → φ v = M.vac v) →
        (∀ v : P, ι v (φ v) = GlobalTheory.StdPairCone.stdB (chrW (α t / β t) (τ v)) (unifAt v.1) (X.c t (splitPrime (τ v))) A.rank A'.rank) →
        ∀ g : SInf D.host.F (Fin A'.rank × Fin (A.rank + A'.rank)),
        X.vac' = thO M ψ (sgn false A').gram (finCongr hr) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac) →
        X.f' t = thO M ψ (sgn false A').gram (finCongr hr) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) := by
  intro D T A A' WW X ψ θ α β νH S hX hr Bs Vs Ws M hp hl t P τ hS b c ι hb hc hι h1 φ hφ hφP hstd g hvac
  have hP : ∀ v, v ∈ P ↔ ∃ w ∈ S t, w.under (𝓞 D.host.F) = v := fun v =>
    ⟨fun hv => ⟨_, (hS _).2 ⟨⟨v, hv⟩, rfl⟩, GlobalTheory.AdelicU.splitPrime_under _⟩, by
      rintro ⟨w, hw, rfl⟩
      obtain ⟨u, rfl⟩ := (hS w).1 hw
      rw [GlobalTheory.AdelicU.splitPrime_under]
      exact u.2⟩
  have hinj : Function.Injective (fun v : P => splitPrime (τ v)) := fun u v h =>
    Subtype.ext ((GlobalTheory.AdelicU.splitPrime_under (τ u)).symm.trans
      ((congrArg (fun w : HeightOneSpectrum (𝓞 D.host.E) => w.under (𝓞 D.host.F)) h).trans (GlobalTheory.AdelicU.splitPrime_under (τ v))))
  obtain ⟨hh1, hh0⟩ := UpperTheory.idempotentSum_fixes_iff_halfEl D (X.e t) (S t) (hX.idem t) P τ hP fun v => (hS _).2 ⟨v, rfl⟩
  have hdet : ∀ v : P, ((Ws.J.map (τ v))ᵀ).det ≠ 0 := fun v => by
    have h0 : Ws.J.det ≠ 0 := by
      rw [hp.JW, Matrix.det_smul, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
      exact mul_ne_zero (pow_ne_zero _ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero) (GlobalTheory.LatVac.gram_det_isUnit WW).ne_zero
    rw [Matrix.det_transpose]
    have h2 := (τ v).toRingHom.map_det Ws.J
    exact fun h => h0 ((τ v).toRingHom.injective ((h2.trans h).trans (map_zero _).symm))
  have hbb : ∀ v : P, -((b v).1ᵀ * Vs.J.map (τ v)) = (X.rA'.β⁻¹).1.map (evW (τ v)) := fun v => by
    have e1 : Vs.J.map (τ v) = -(A'.gram.map (τ v)) := by
      rw [hp.JV]
      refine Matrix.ext fun i j => ?_
      simp
    have e2 : (b v).1ᵀ * (A'.gram.map (τ v) * X.rA'.β.1.map (evW (τ v))) = 1 := by
      rw [← Matrix.transpose_transpose (A'.gram.map (τ v) * _), ← hb v, ← Matrix.transpose_mul, Units.inv_mul,
        Matrix.transpose_one]
    have e3 : X.rA'.β.1.map (evW (τ v)) * (X.rA'.β⁻¹).1.map (evW (τ v)) = 1 := by
      rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [e1, Matrix.mul_neg, neg_neg, ← Matrix.mul_one (_ * A'.gram.map (τ v)), ← e3, ← Matrix.mul_assoc,
      Matrix.mul_assoc (b v).1ᵀ, e2, Matrix.one_mul]
  refine UpperTheory.exists_isSBHalf_theta_of_selfDual_lattices D ψ false A' WW _ (finCongr hr) Bs Vs Ws M hp X.rA'.Λ X.rW.Λ hl hX.rigA'.1 hX.rigW.1 P
    (fun v => (τ v).comp D.sp.cm.sig) τ (fun v x => congrArg (τ v) (star_star x).symm) (cA D (X.e t)) hh0
    (fun z => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hh1 z)
    (fun v => Matrix.GeneralLinearGroup.map (evW (τ v)) X.rA'.β⁻¹)
    (fun v => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet v) * c v) ι (fun v => ?_) h1 φ hφ hφP g
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (α t / β t) (X.e t) (X.ideal S t) A.rank A' WW X.rA'.β X.rW.β) (X.f' t) (fun x => ?_) ?_
  · have h := hι v
    unfold Model.IsLinBar at h
    convert h using 1
    funext u
    change (X.rA'.β⁻¹).1.map (evW (τ v)) * _ * ((Ws.J.map (τ v))ᵀ * (c v).1) = _
    rw [← hbb v]
    simp only [Matrix.neg_mul, Matrix.mul_assoc]
  · by_cases hx : IsHalf (cA D (X.e t)) x
    · rw [if_pos hx]
      refine (UpperTheory.stdSectionSecond_eq_prod_local D (X.e t) (S t) (hX.idem t) P (fun v => v.1) τ hS hinj (X.c t) (α t / β t) A.rank A' WW
        X.rA'.β X.rW.β hr x hx).trans (Finset.prod_congr rfl fun v _ => ?_)
      rw [hstd v, ← coord_eq, ← hc v, ← hp.JW, Matrix.mul_assoc]
      rfl
    · rw [if_neg hx]
      exact if_neg fun h => hx h.1
  · rw [← hvac]
    exact hX.snd t
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem fmFst_mat {k : Type} [Field k] {a n d : ℕ} (e : Fin n ≃ Fin d) (B G Gi : Matrix (Fin a) (Fin a) k) (hG : Gi * G = 1)
    (W Wi : Matrix (Fin d) (Fin d) k) (hW : Wi * W = 1) (m : GL (Fin n) k) (hm : m.1 = W.submatrix e e)
    (X : Matrix (Fin d) (Fin a) k) :
    (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e * (GlobalTheory.SplitFlip.invT m).1 = ((Wi * X * B)ᵀ).submatrix id e := by
  have h1 : (m⁻¹).1 = Wi.submatrix e e := by
    have : Wi.submatrix e e * m.1 = 1 := by
      rw [hm, Matrix.submatrix_mul_equiv, hW]; exact Matrix.submatrix_one_equiv e
    calc (m⁻¹).1 = (Wi.submatrix e e * m.1) * (m⁻¹).1 := by rw [this, Matrix.one_mul]
      _ = Wi.submatrix e e := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have h2 : (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e = ((X * B)ᵀ).submatrix id e := by
    have : (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e = ((G * B)ᵀ * (X * Gi)ᵀ).submatrix id e := rfl
    rw [this, ← Matrix.transpose_mul, Matrix.mul_assoc X, ← Matrix.mul_assoc Gi, hG, Matrix.one_mul]
  rw [h2, GlobalTheory.SplitFlip.invT_val, h1, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul,
    Matrix.mul_assoc]

private theorem selfDual_neg {D : D7} {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (h : IsSelfDualC V Λ) : IsSelfDualC (sgn true V) Λ := by
  refine ⟨h.1, fun y => (h.2 y).trans (forall₂_congr fun x _ => ?_)⟩
  have e : ∑ i, ∑ j, star (x i) * (sgn true V).gram i j * y j = -∑ i, ∑ j, star (x i) * V.gram i j * y j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    show star (x i) * (-V.gram i j) * y j = _
    ring
  rw [e]
  exact ⟨fun ⟨b, hb⟩ => ⟨-b, by simp [hb]⟩, fun ⟨b, hb⟩ => ⟨-b, by simp [hb]⟩⟩

theorem UpperTheory.thetaLift_triple_local_split_places :
    ∀ (D : D7) (T : Type) (A A' WW : HSp D) (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
        (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))),
        X.Is ψ θ α β νH S → ∀ (hr : A.rank + A'.rank = WW.rank) (Bs : Base D.host.F D.host.E)
        (Vs : Spc D.host.F D.host.E A.rank) (Ws : Spc D.host.F D.host.E (A.rank + A'.rank)) (M : Model D.sp.cm.sig Vs Ws),
        IsPair ψ true A WW (finCongr hr) Bs Vs Ws M → IsLat (finCongr hr) Vs Ws X.rA.Λ X.rW.Λ →
        ∀ (t : T) (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (τ : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v),
        (∀ w, w ∈ S t ↔ ∃ v : P, splitPrime (τ v) = w) →
        ∀ (b : ∀ v : P, GL (Fin A.rank) (Fv D.host.F v)) (c : ∀ v : P, GL (Fin (A.rank + A'.rank)) (Fv D.host.F v))
          (ι : ∀ v : P, ((Fin A.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ) →ₗ[ℂ]
            (Matrix (Fin A.rank) (Fin (A.rank + A'.rank)) (Fv D.host.F v) → ℂ)),
        (∀ v, ((b v)⁻¹).1 = -(A.gram.map (τ v) * X.rA.β.1.map (evW (τ v)))ᵀ) →
        (∀ v, (c v).1 = (X.rW.β.1.map (evW (τ v))).submatrix (finCongr hr) (finCongr hr)) →
        (∀ v, M.IsLinW ψ (τ v) (b v) (c v) (ι v)) → (∀ v : P, ι v (M.vac v) 0 = 1) →
        ∀ (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin A.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ v, v ∉ P → φ v = M.vac v) →
        (∀ v : P, ι v (φ v) = GlobalTheory.StdPairCone.stdA (chrW (α t / β t) (τ v)) (unifAt v.1) (X.c t (splitPrime (τ v))) A.rank A'.rank) →
        ∀ g : SInf D.host.F (Fin A.rank × Fin (A.rank + A'.rank)),
        X.vac = thO M ψ (sgn true A).gram (finCongr hr) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac) →
        X.f t = thO M ψ (sgn true A).gram (finCongr hr) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) := by
  intro D T A A' WW X ψ θ α β νH S hX hr Bs Vs Ws M hP hL t P τ hS b c ι hb hc hι hι0 φ hφ hφ' hφA g hvac
  have hPS : ∀ v, v ∈ P ↔ ∃ w ∈ S t, w.under (𝓞 D.host.F) = v := fun v => by
    constructor
    · intro hv
      exact ⟨splitPrime (τ ⟨v, hv⟩), (hS _).2 ⟨_, rfl⟩, GlobalTheory.AdelicU.splitPrime_under (τ ⟨v, hv⟩)⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨u, rfl⟩ := (hS w).1 hw
      rw [GlobalTheory.AdelicU.splitPrime_under (τ u)]
      exact u.2
  have hτS : ∀ v : P, splitPrime (τ v) ∈ S t := fun v => (hS _).2 ⟨v, rfl⟩
  have hinj : Function.Injective fun v : P => splitPrime (τ v) := fun u v h => by
    have h1 := GlobalTheory.AdelicU.splitPrime_under (τ u)
    have h2 := GlobalTheory.AdelicU.splitPrime_under (τ v)
    have h' : splitPrime (τ u) = splitPrime (τ v) := h
    exact Subtype.ext (h1.symm.trans (h' ▸ h2))
  obtain ⟨hh0, hh1⟩ := UpperTheory.idempotentSum_fixes_iff_halfEl D (X.e t) (S t) (hX.idem t) P τ hPS hτS
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin A.rank) (Fin A.rank) D.host.E, G = (sgn true A).gram := ⟨_, rfl⟩
  have hdet : IsUnit G.det := by rw [hG]; exact (Formalism.L2.Theta.gram_det_ne (sgn true A)).isUnit
  have hGi : ∀ v : P, (G⁻¹.map (incA D)).map (piW (τ v)) * (G.map (incA D)).map (piW (τ v)) = 1 := fun v => by
    rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hbG : ∀ v : P, ((b v)⁻¹).1 = ((G.map (incA D)).map (piW (τ v)) * X.rA.β.1.map (evW (τ v)))ᵀ := fun v => by
    have e0 : (G.map (incA D)).map (piW (τ v)) = -A.gram.map (τ v) := by
      refine Matrix.ext fun i j => ?_
      have e1 : G i j = -A.gram i j := by rw [hG]; rfl
      have e2 : ∀ y, piW (τ v) (incA D y) = τ v y := fun y => one_mul (τ v y)
      show piW (τ v) (incA D (G i j)) = -(τ v (A.gram i j))
      rw [e2, e1, map_neg]
    rw [hb, e0, Matrix.neg_mul, Matrix.transpose_neg]
  have key : ∀ (x : WO A WW) (v : P),
      ((b v)⁻¹).1 * (ptO (sgn true A).gram (finCongr hr) x).map (piW (τ v)) * (GlobalTheory.SplitFlip.invT (c v)).1 =
      (((frMapO A WW X.rA.β X.rW.β x).map (evW (τ v)))ᵀ).submatrix id (finCongr hr) := fun x v => by
    have e1 : (ptO G (finCongr hr) x).map (piW (τ v)) =
        ((Matrix.map x (piW (τ v)) * (G⁻¹.map (incA D)).map (piW (τ v)))ᵀ).submatrix id (finCongr hr) := by
      rw [← Matrix.map_mul]; rfl
    have e2 : (frMapO A WW X.rA.β X.rW.β x).map (evW (τ v)) =
        (X.rW.β⁻¹).1.map (evW (τ v)) * Matrix.map x (piW (τ v)) * X.rA.β.1.map (evW (τ v)) := by
      unfold frMapO
      rw [Matrix.map_mul, Matrix.map_mul]
      congr 2
      refine Matrix.ext fun i j => ?_
      exact GlobalTheory.BotMatch.evW_toEAf (τ v) (x i j)
    rw [← hG, hbG, e1, e2]
    refine fmFst_mat (finCongr hr) _ _ _ (hGi v) (X.rW.β.1.map (evW (τ v))) _ ?_ (c v) (hc v) _
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hth := hX.fst t
  rw [hvac] at hth
  refine UpperTheory.exists_isSBHalf_theta_of_selfDual_lattices D ψ true A WW _ (finCongr hr) Bs Vs Ws M hP X.rA.Λ X.rW.Λ hL (selfDual_neg hX.rigA.1) hX.rigW.1
    P τ (fun v => (τ v).comp D.sp.cm.sig) (fun _ _ => rfl) (X.e t) hh0 hh1 (fun v => (b v)⁻¹)
    (fun v => GlobalTheory.SplitFlip.invT (c v)) ι (fun v => hι v) hι0 φ hφ hφ' g
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (α t / β t) (X.e t) (X.ideal S t) A WW X.rA.β X.rW.β) (X.f t) (fun x => ?_) hth
  by_cases hx : IsHalf (X.e t) x
  · rw [if_pos hx]
    refine (UpperTheory.stdSectionFirst_eq_prod_local D (X.e t) (S t) (hX.idem t) P (fun v => v.1) τ hS hinj (X.c t) (α t / β t) A WW X.rA.β X.rW.β
      A'.rank hr x hx).trans (Finset.prod_congr rfl fun v _ => ?_)
    rw [hφA v]
    exact congrArg _ (key x v).symm
  · rw [if_neg hx]
    exact if_neg fun h => hx h.1
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative

private theorem cont_cEmb {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (τ : E →+* ℂ) :
    Continuous (cEmb (E := E) (n := n) τ) := by
  have c0 : Continuous (coord τ) := by
    unfold coord
    split_ifs
    · exact continuous_apply _
    · exact Complex.continuous_conj.comp (continuous_apply _)
  have c2 : Continuous (infEq E).symm := by
    refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  have c3 : Continuous (pInf E) := c2.comp continuous_fst
  have c4 : Continuous fun a => coord τ (pInf E a) := c0.comp c3
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.comp continuous_subtype_val).matrix_map c4
  · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map c4

theorem UpperTheory.exists_unitaryAutomorphicForm_of_weightVectorValued :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (emb : ι → (E →+* ℂ)), Function.Injective (fun τ => InfinitePlace.mk (emb τ)) →
        ∀ (mu : ι → ℕ → ℕ) (sh : ι → ℤ) (lam : ι → DomWeight n), (∀ τ (a : Fin n), (lam τ).w a = (mu τ a : ℤ) + sh τ) →
        ∀ (B : (UA E n → ℂ) →ₗ⋆[ℂ] (UA E n → ℂ) →ₗ[ℂ] ℂ), (∀ φ, IsAutFormU φ → φ ≠ 0 → 0 < (B φ φ).re) →
        (∀ k ∈ finU (E := E) (n := n), ∀ φ ψ, IsAutFormU φ → IsAutFormU ψ → B (RU E n k φ) (RU E n k ψ) = B φ ψ) →
        ∀ F1 : UA E n → NablaT ℂ n mu, F1 ≠ 0 →
        (∀ γ ∈ ratU E n, ∀ g, F1 (γ * g) = wtOp ℂ n mu sh (fun τ => cEmb (emb τ) γ) (F1 g)) →
        (∀ x ∈ infU E n, ∀ g, F1 (g * x) = F1 g) → (∀ᶠ y in nhds (1 : UA E n), ∀ g, F1 (g * y) = F1 g) →
        ∃ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π ∧ (∀ τ, HasWeightAt π (emb τ) (lam τ)) ∧ ∃ φ ∈ π, φ ≠ 0 ∧
          ∀ (κ : Type) (s : Finset κ) (y : κ → UA E n) (c : ℂ), (∀ i ∈ s, y i ∈ finU (E := E) (n := n)) →
            (∀ g, ∑ i ∈ s, F1 (g * y i) = c • F1 g) → ∑ i ∈ s, RU E n (y i) φ = c • φ := by
  intro E _ _ _ n ι _ _ emb hinj mu sh lam hl B hpos hinv F1 hF0 hrat hinf hev
  let C : UA E n →* (ι → GL (Fin n) ℂ) := MonoidHom.pi fun τ => cEmb (E := E) (n := n) (emb τ)
  let R : UA E n →* Module.End ℂ (NablaT ℂ n mu) := (wtHom ℂ n mu sh).comp C
  have hR : ∀ g, R g = wtOp ℂ n mu sh (C g) := fun _ => rfl
  have hRfin : ∀ k ∈ finU (E := E) (n := n), R k = 1 := fun k hk => by
    have h1 : C k = 1 := by
      funext τ
      change Matrix.GeneralLinearGroup.map (coord (emb τ)) (cInf k) = 1
      rw [MonoidHom.mem_ker.1 hk, map_one]
    rw [hR, h1, wtOp_one]
  obtain ⟨hfd, hcont⟩ := UpperTheory.finiteDimensional_nablaT_and_continuous_wtOp n ι mu sh
  have hC : Continuous C := continuous_pi fun τ => cont_cEmb (emb τ)
  obtain ⟨P, hP0, hP⟩ := UpperTheory.exists_invariant_nondegenerate_pairing_weightRep_nablaT n ι mu sh lam hl
  let f : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] (UA E n → ℂ) :=
    { toFun := fun v g => P v (R g⁻¹ (F1 g))
      map_add' := fun a b => funext fun g => by simp
      map_smul' := fun a b => funext fun g => by simp }
  have hf : ∀ v g, f v g = P v (R g⁻¹ (F1 g)) := fun _ _ => rfl
  have hRU : ∀ (x : UA E n) (φ : UA E n → ℂ) (g : UA E n), RU E n x φ g = φ (g * x) := fun _ _ _ => rfl
  have hfa : ∀ v, IsAutFormU (f v) := fun v =>
    UpperTheory.isAutFormU_of_vectorValued_invariant E n (NablaT ℂ n mu) R hRfin (fun ℓ u => (hcont ℓ u).comp hC) F1 hrat hinf hev (P v)
  have hfe : ∀ x ∈ infU E n, ∀ v, f (Formalism.L2.DIV.rhoK lam (C x) v) = RU E n x (f v) := fun x hx v => by
    funext g
    rw [hRU, hf, hf, hinf x hx, ← hP (C x) v (R (g * x)⁻¹ (F1 g)), ← hR, ← Module.End.mul_apply, ← map_mul,
      mul_inv_rev, mul_inv_cancel_left]
  have hf0 : f ≠ 0 := fun h0 => hF0 (funext fun g => by
    have h1 : R g⁻¹ (F1 g) = 0 := hP0 _ fun v => by rw [← hf, h0]; rfl
    have h2 := congrArg (R g) h1
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, map_zero] at h2
    exact h2)
  haveI : Nontrivial (Formalism.L2.DIV.VV ℂ lam) := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact hf0 (LinearMap.ext fun v => by rw [Subsingleton.elim v 0, map_zero, map_zero])
  haveI : ∀ v, Finite (Formalism.GradedWeylDivisibility.ssIdx n n (lam v).natW) := fun _ => (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  haveI : FiniteDimensional ℂ (Formalism.L2.DIV.VV ℂ lam) := Module.Finite.of_basis (Formalism.L2.DIV.bVV ℂ lam)
  obtain ⟨π, hπ, f', hf'0, hf'π, hf'e, hsum⟩ := UpperTheory.exists_admissible_equivariantFormsRep E n (Formalism.L2.DIV.VV ℂ lam)
    ((Formalism.L2.DIV.rhoK (K := ℂ) lam).comp (C.comp (infU E n).subtype)) (UpperTheory.span_highestWeightRep_unitaryGroup_realPoints_image_eq_top E n ι emb hinj lam) B hpos hinv
    f hf0 hfa (fun x v => hfe x.1 x.2 v)
  obtain ⟨v, hv⟩ : ∃ v, f' v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hf'0 (LinearMap.ext hc)
  refine ⟨π, hπ, UpperTheory.hasWeightAt_of_ne_zero_intertwining E n ι emb hinj lam π f' hf'0 hf'π (fun x hx v => hf'e ⟨x, hx⟩ v), f' v, hf'π v, hv,
    fun κ s y c hy hs => hsum κ s y c hy (fun w => ?_) v⟩
  funext g

  rw [Finset.sum_apply, Pi.smul_apply, hf, ← map_smul, ← map_smul, ← hs g, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hRU, hf, mul_inv_rev, map_mul, hRfin _ ((finU (E := E) (n := n)).inv_mem (hy i hi)), one_mul]
end
