module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle292
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle311
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle560
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle139
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle312
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle141
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle313
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle314
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ConjLine

theorem weil_source_line_opposite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E), L.rank = L'.rank → τᴴ ⬝ (L.gram ⬝ τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram → ∀ (χz χ χ' : ((AE D)ˣ →* Circle)) (om : Om L S) (om' : Om S L'), IsWeilDatumO ψ L S χz χ om → IsWeilDatumO ψ S L' χ' χz⁻¹ om' → ∀ f, IsThetaFunO ψ L S f → IsThetaFunO ψ S L' (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w))) ∧ ∀ h, om' (h, 1) (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w))) = fun w => om (1, h) f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)) := by
  intro D ψ L L' S τ hrk hg χz χ χ' om om' hom hom' f hf
  have hstd : IsStdChar D ψ (-1) := hom.std
  have CA := GlobalTheory.T.weilConjugationAdjointRule_standard_char D ψ hstd S L'
  have h1 := (CA.conj_target χ' χz⁻¹ om' hom').1
  rw [inv_inv] at h1
  have hg' : τᴴ ⬝ (L.gram ⬝ τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • (GlobalTheory.ChiGrid.negSp L').gram := by
    rw [hg, GlobalTheory.ChiGrid.negSp_gram]; simp
  have H := GlobalTheory.T.weilRep_conj_sourceLine_eq_targetLine D ψ L (GlobalTheory.ChiGrid.negSp L') S τ hrk hg' χz χ χ'⁻¹ om (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget om') hom h1 f hf
  refine ⟨?_, ?_⟩
  · have := H.1
    exact (CA.theta_neg _).1.mp this
  · intro h
    have key : ∀ F : WO S L' → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget om' (h, 1) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id F) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (om' (h, 1) F) := by
      intro F
      have e := GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cjEnd_cj (Equiv.refl (WO S L')) (om' (h, (GlobalTheory.ChiGrid.negGA L').symm 1)) F
      simpa [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget] using e
    have H2 := H.2 h
    have K : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget om' (h, 1) (fun w => star (f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)))) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (om' (h, 1) (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)))) := key (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)))
    rw [K] at H2
    funext w
    have := congrArg star (congrFun H2 w)
    simpa [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj] using this

end GlobalTheory.ConjLine
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

theorem _root_.GlobalTheory.T.definite_real_group_fixes_split_space_weil_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (t : ℕ) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) 1) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → HSpace.SigOK H → H.rank = 2 * t → (∀ τ, H.sig τ = (t, t)) → ∀ f, IsThetaFunO ψ A H f → (∀ τ, IsFockVacAt (heisO ψ A H) θ τ (cplxO 1 (sH τ)) f) → ∀ b ∈ GinfC A, om (b, 1) f = f := by
  first | exact @GlobalTheory.VacuumSplitReal.vacuum_fixed | exact GlobalTheory.VacuumSplitReal.vacuum_fixed | (intros; apply GlobalTheory.VacuumSplitReal.vacuum_fixed <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.CongAtIdem

theorem read_rel {A B K E : Type} [CommRing A] [CommRing B] [CommRing K] [CommRing E] {m n : Type} [Fintype m] [Fintype n]
    (t : A →+* B) (φ : B →+* K) (i : E →+* A) (j : E →+* B) (hij : ∀ x, t (i x) = j x) {e : A} (he : φ (t e) = 1)
    (X : Matrix m m A) (Z : Matrix n n A) (γ γ₀ : Matrix m n E) (v : Matrix m n A) (k : ℕ)
    (h : γ₀.map (fun r => e * i r) = X * γ.map (fun r => e * i r) * Z + k • v) (r : m) (s : n) :
    φ ((X.map t * γ.map j * Z.map t - γ₀.map j) r s) = -((k : K) * φ (t (v r s))) := by
  have h1 := congrArg (fun W : Matrix m n A => φ (t (W r s))) h

  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, map_add (f := _), map_sum, map_mul, he,
  one_mul, hij, nsmul_eq_mul, map_natCast] at h1

  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, map_mul, h1]
  ring

end GlobalTheory.AdForm.CongAtIdem

namespace GlobalTheory.AdForm.CongAtIdem

variable {D : D7}

theorem adAt_toEAf_of_isIdemAt {f : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hf : Formalism.L2.NTheta.IsIdemAt f P) : adAt D.host.F P (toEAf D f) = 1 := by
  let ι : Af D.host.F ⊗[D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv.trans (afIso D.host.F D.host.E)
  have h1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x := fun x =>
    afIso_tmul_one D.host.F D.host.E x
  have h2 : ∀ y, y ∈ intAE D ↔ ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y Q) ≤ 1 := fun y =>
    (GlobalTheory.IdemSupport.mem_intAE_iff y).trans (mem_rInt_iff D.host.F D.host.E _)
  exact GlobalTheory.ChrOff.comp_idem ι h1 h2 hf

theorem adAt_toEAf_of_isIdemSum {e : AE D} {Ps : Finset (HeightOneSpectrum (𝓞 D.host.E))}
    (he : IsIdemSum e Ps) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ Ps) :
    adAt D.host.F P (toEAf D e) = 1 := by
  obtain ⟨a, ha, hae⟩ := GlobalTheory.OffIdem.idemSum_mul_idemAt he hP
  have h := congrArg (fun z => adAt D.host.F P (toEAf D z)) hae
  simp only [map_mul, adAt_toEAf_of_isIdemAt ha, one_mul] at h
  exact h

end GlobalTheory.AdForm.CongAtIdem

namespace GlobalTheory.AdForm.CongAtIdem

variable {D : D7}

theorem isIntegral_of_eq {x : D.host.E} (h : ∃ r : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E r = x) :
    IsIntegral ℤ x := by
  obtain ⟨r, rfl⟩ := h
  exact r.2

theorem tmul_one_mem_rInt {x : D.host.E} (hx : IsIntegral ℤ x) :
    x ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∈ Formalism.L2.DIV.RInt D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨x, ⟨⟨x, hx⟩, rfl⟩⟩, rfl⟩)

theorem one_tmul_mem_rInt {α : FiniteAdeleRing (𝓞 D.host.F) D.host.F} (hα : α ∈ intAf D.host.F) :
    (1 : D.host.E) ⊗ₜ[D.host.F] α ∈ Formalism.L2.DIV.RInt D.host.F D.host.E :=
  Subring.subset_closure (Or.inr ⟨⟨α, fun v => hα v⟩, rfl⟩)

theorem exists_den_stdHom (S T : HSp D) : ∃ d : ℕ, 0 < d ∧ ∀ v ∈ stdHom S T, ∀ r s,
    ((d : EF D) * toEAf D (v r s) : Formalism.L2.DIV.AfE D.host.F D.host.E) ∈ Formalism.L2.DIV.RInt D.host.F D.host.E := by
  obtain ⟨a0, ha0, hfrac⟩ := D.host.AA.isFractional
  have ha0' : ((a0 : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    intro h
    exact nonZeroDivisors.coe_ne_zero ⟨a0, ha0⟩ (RingOfIntegers.coe_eq_zero_iff.1 h)
  obtain ⟨d, hd, hint⟩ := GlobalTheory.AdeleBaseChange.exists_nat_mul_integral
    (insert ((a0 : D.host.E))⁻¹ (Finset.image (fun p : Fin S.rank × Fin S.rank => S.gram p.1 p.2) Finset.univ))
  have hx0 : IsIntegral ℤ ((d : D.host.E) * ((a0 : D.host.E))⁻¹) := by
    rw [← nsmul_eq_mul]; exact isIntegral_of_eq (hint _ (Finset.mem_insert_self _ _))
  have hG : ∀ k j, IsIntegral ℤ ((d : D.host.E) * S.gram k j) := fun k j => by
    rw [← nsmul_eq_mul]
    exact isIntegral_of_eq (hint _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(k, j), Finset.mem_univ _, rfl⟩)))
  refine ⟨d * d, Nat.mul_pos hd hd, fun v hv => ?_⟩
  induction hv using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    intro r c
    have hint' : IsIntegral ℤ (((d * d : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c)) := by
      have hA : IsIntegral ℤ ((a0 : D.host.E) * a) := by
        obtain ⟨y, hy⟩ := hfrac a ha
        refine isIntegral_of_eq ⟨y, ?_⟩
        rw [hy, Algebra.smul_def]
      have hsum : IsIntegral ℤ (∑ k, star (s k) * ((d : D.host.E) * S.gram k c)) :=
        IsIntegral.sum _ fun k _ => IsIntegral.mul
          ((hs k).map (starRingEnd D.host.E).toIntAlgHom) (hG k c)
      have e : ((d * d : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c) =
          ((d : D.host.E) * ((a0 : D.host.E))⁻¹) * ((a0 : D.host.E) * a) * t r *
            ∑ k, star (s k) * ((d : D.host.E) * S.gram k c) := by
        have hx : ((a0 : D.host.E))⁻¹ * (a0 : D.host.E) = 1 := inv_mul_cancel₀ ha0'
        have e2 : ∑ k, star (s k) * ((d : D.host.E) * S.gram k c) = (d : D.host.E) * ∑ k, star (s k) * S.gram k c := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        rw [e2]; push_cast
        linear_combination (-((d : D.host.E) * d * a * t r * ∑ k, star (s k) * S.gram k c)) * hx
      rw [e]
      exact ((hx0.mul hA).mul (ht r)).mul hsum
    change ((d * d : ℕ) : EF D) * ((a * t r * ∑ k, star (s k) * S.gram k c) ⊗ₜ[D.host.F] α) ∈ _
    have e3 : ((d * d : ℕ) : EF D) * ((a * t r * ∑ k, star (s k) * S.gram k c) ⊗ₜ[D.host.F] α) =
        ((((d * d : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c)) ⊗ₜ[D.host.F]
          (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] α) := by
      have hc : ((d * d : ℕ) : EF D) = ((d * d : ℕ) : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
        (map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (A := D.host.E)
          (B := FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (d * d)).symm
      rw [hc]
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e3]
    exact mul_mem (tmul_one_mem_rInt hint') (one_tmul_mem_rInt hα)
  | zero => intro r s; simp
  | add x y _ _ hx hy => intro r s; rw [Matrix.add_apply, RingHom.map_add (toEAf D), mul_add]; exact add_mem (hx r s) (hy r s)
  | neg x _ hx => intro r s; rw [Matrix.neg_apply, RingHom.map_neg (toEAf D), mul_neg]; exact neg_mem (hx r s)

end GlobalTheory.AdForm.CongAtIdem

namespace GlobalTheory.AdForm.CongAtIdem

variable {D : D7}

theorem finM_rfl (V : HSp D) (x : GA D V) : finM V rfl x = (Formalism.L2.Theta.mt V x).map (toEAf D) := by
  simp [finM, finCongr_refl]

theorem mt_mul' (V : HSp D) (x y : GA D V) :
    Formalism.L2.Theta.mt V (x * y) = Formalism.L2.Theta.mt V x * Formalism.L2.Theta.mt V y := by
  show (matHom V (x * y)).1 = (matHom V x).1 * (matHom V y).1
  rw [map_mul, Units.val_mul]

theorem mt_one' (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  show (matHom V 1).1 = 1
  rw [map_one, Units.val_one]

theorem inv_val_eq (V : HSp D) (x : GA D V) (Y : GL (Fin V.rank) (EF D)) (hY : finM V rfl x = Y.1) :
    (Y⁻¹ : GL (Fin V.rank) (EF D)).1 = (Formalism.L2.Theta.mt V x⁻¹).map (toEAf D) := by
  have h1 : (Formalism.L2.Theta.mt V x⁻¹).map (toEAf D) * Y.1 = 1 := by
    rw [← hY, finM_rfl, ← Matrix.map_mul, ← mt_mul', inv_mul_cancel, mt_one',
      Matrix.map_one _ (map_zero _) (map_one _)]
  calc (Y⁻¹ : GL (Fin V.rank) (EF D)).1
      = ((Formalism.L2.Theta.mt V x⁻¹).map (toEAf D) * Y.1) * (Y⁻¹ : GL (Fin V.rank) (EF D)).1 := by
        rw [h1, Matrix.one_mul]
    _ = (Formalism.L2.Theta.mt V x⁻¹).map (toEAf D) := by
        rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

end GlobalTheory.AdForm.CongAtIdem

namespace GlobalTheory.AdForm.CongAtIdem

theorem cong_at_idem : ∀ {D : D7} (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (e : AE D)
    (Ps : Finset (HeightOneSpectrum (𝓞 D.host.E))), IsIdemSum e Ps → ∃ d : ℕ, 0 < d ∧
    ∀ (g : GA D S) (h : GA D T) (Y : GL (Fin a) (EF D)) (Y' : GL (Fin b) (EF D)), finM S hS g = Y.1 → finM T hT h = Y'.1 →
    ∀ (M : ℕ) (γ γ₀ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (v : WO S T), v ∈ stdHom S T →
      γ₀.map (fun r => e * incA D r) = actO S T g⁻¹ h⁻¹ (γ.map fun r => e * incA D r) + (d * M) • v →
      ∀ P ∈ Ps, ∀ r s, Valued.v (adAt D.host.F P
        ((HMul.hMul (HMul.hMul ((Y'⁻¹ : GL (Fin b) (EF D)).1 : Matrix (Fin b) (Fin b) (EF D))
          (((LinearMap.toMatrix' (toHom S T hS hT γ)).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Matrix (Fin b) (Fin a) (EF D))))
          (Y.1 : Matrix (Fin a) (Fin a) (EF D)) -
          ((LinearMap.toMatrix' (toHom S T hS hT γ₀)).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Matrix (Fin b) (Fin a) (EF D))) r s)) ≤
        Valued.v ((M : ℕ) : P.adicCompletion D.host.E) := by
  intro D S T a b hS hT e Ps he
  subst hS; subst hT
  obtain ⟨d, hd, hden⟩ := exists_den_stdHom S T
  refine ⟨d, hd, ?_⟩
  intro g h Y Y' hY hY' M γ γ₀ v hv hH P hP r s
  rw [← hY, finM_rfl, inv_val_eq T h Y' hY']
  simp only [toHom, LinearMap.toMatrix'_toLin', finCongr_refl, Matrix.reindex_refl_refl]
  rw [actO, inv_inv] at hH
  have key := read_rel (toEAf D) (adAt D.host.F P) (incA D)
    (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (fun _ => rfl)
    (adAt_toEAf_of_isIdemSum he hP) _ _ γ γ₀ v (d * M) hH r s
  have hint : Valued.v (adAt D.host.F P ((d : EF D) * toEAf D (v r s))) ≤ 1 :=
    (mem_rInt_iff D.host.F D.host.E _).1 (hden v hv r s) P
  rw [RingHom.map_mul, map_natCast (adAt D.host.F P)] at hint
  refine (congrArg Valued.v key).trans_le ?_
  rw [Valuation.map_neg, Nat.cast_mul, mul_right_comm, Valuation.map_mul]
  exact mul_le_of_le_one_left' hint

end GlobalTheory.AdForm.CongAtIdem
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.CocycleSS
open GlobalTheory.LatVac

variable {D : D7}

theorem natCast_smul_mem_of_halfAO {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c)
    {x : Formalism.L2.Col.HomE E a b} (hx : x ∈ halfAO SS M c) : (c : E) • x ∈ M := by
  refine GlobalTheory.ThetaMove.mem_of_locP fun Q => ?_
  have h : ((c : E) ^ (-expS SS Q))⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := (Submodule.mem_iInf _).1 hx Q
  have hc' : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have key : ∀ k : ℕ, (c : E) = (c : E) ^ k * ((c : E) ^ (-expS SS Q))⁻¹ →
      (c : E) • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := fun k hk => by
    have := nsmul_mem h (c ^ k)
    rwa [← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← hk] at this
  unfold expS at key
  split_ifs at key
  · exact key 0 (by simp)
  · exact key 2 (by rw [neg_neg, zpow_one]; field_simp)
  · exact key 1 (by simp)

theorem conjP_conjP (Q : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ (Formalism.L2.Col.conjPrime₂ Q) = Q := by
  apply HeightOneSpectrum.ext
  ext r
  rw [Formalism.L2.Col.mem_conjP, Formalism.L2.Col.mem_conjP, Formalism.L2.Col.cO_cO]

theorem conjP_not_mem {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e SS)
    {PP : HeightOneSpectrum (𝓞 D.host.E)} (hPP : PP ∈ SS) : Formalism.L2.Col.conjPrime₂ PP ∉ SS := fun h' =>
  GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum h PP hPP _ h' fun r hr =>
    ⟨Formalism.L2.Col.cO D.host.E r, by rw [Formalism.L2.Col.mem_conjP, Formalism.L2.Col.cO_cO]; exact hr, rfl⟩

end GlobalTheory.AdForm.CocycleSS

namespace GlobalTheory.AdForm.CocycleSS
open GlobalTheory.LatVac

variable {D : D7} {S T : HSp D}

theorem smul_tmul_fin {a : AE D} (ha : infPart D a = 0) (r : D.host.E) :
    a * ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] r) = a * incA D r :=
  GlobalTheory.SplitScalar.adele_ext (by rw [RingHom.map_mul, RingHom.map_mul, ha, zero_mul, zero_mul])
    (by rw [RingHom.map_mul, RingHom.map_mul]; rfl)

theorem symplOH_smul (a : AE D) (x y : WO S T) : symplOH S T (a • x) y = symplOH S T x (cA D a • y) := by
  rw [symplOH, symplOH, GlobalTheory.SplitScalar.symplO_smul]

theorem lhs_eq {e : AE D} (hinf : infPart D (cA D e) = 0) (hec : e * cA D e = 0)
    (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplOH S T (X.map fun r => e * incA D r) (GlobalTheory.VacUnique.finRat S T X - X.map fun r => e * incA D r) =
      symplOH S T (X.map (incA D)) (cA D e • X.map (incA D)) := by
  have hXt : (X.map fun r => e * incA D r : WO S T) = e • (X.map (incA D) : WO S T) := by ext i j; rfl
  have hF : cA D e • GlobalTheory.VacUnique.finRat S T X = cA D e • (X.map (incA D) : WO S T) := by
    ext i j; exact smul_tmul_fin hinf _
  rw [hXt, symplOH_smul, smul_sub, hF, smul_smul, mul_comm, hec, zero_smul, sub_zero]

theorem smul_finRat_natCast {e : AE D} (hinf : infPart D e = 0) (c : ℕ) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    e • GlobalTheory.VacUnique.finRat S T ((c : D.host.E) • X) = (e * incA D (c : D.host.E)) • (X.map (incA D) : WO S T) := by
  ext i j
  show e * ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] ((c : D.host.E) * X i j)) = (e * incA D (c : D.host.E)) * incA D (X i j)
  rw [smul_tmul_fin hinf, map_mul, mul_assoc]

theorem smul_map_inv {e : AE D} (hcc : cA D e * cA D e = cA D e) (c : ℕ) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    cA D e • (((c : D.host.E)⁻¹ • X).map fun r => cA D e * incA D r : WO S T) =
      (cA D e * incA D ((c : D.host.E)⁻¹)) • (X.map (incA D) : WO S T) := by
  ext i j
  show cA D e * (cA D e * incA D ((c : D.host.E)⁻¹ * X i j)) = (cA D e * incA D ((c : D.host.E)⁻¹)) * incA D (X i j)
  rw [map_mul, ← mul_assoc, hcc, mul_assoc]

theorem cA_incA_natCast (c : ℕ) : cA D (incA D (c : D.host.E)) = incA D (c : D.host.E) := by
  show incA D (star (c : D.host.E)) = _
  rw [star_natCast]

theorem rhs_eq {e : AE D} (hinf : infPart D e = 0) (hcc : cA D e * cA D e = cA D e) {c : ℕ} (hc : 0 < c)
    (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplOH S T (e • GlobalTheory.VacUnique.finRat S T ((c : D.host.E) • X))
        (cA D e • (((c : D.host.E)⁻¹ • X).map fun r => cA D e * incA D r : WO S T)) =
      symplOH S T (X.map (incA D)) (cA D e • X.map (incA D)) := by
  have hcE : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hs : cA D e * incA D (c : D.host.E) * (cA D e * incA D ((c : D.host.E)⁻¹)) = cA D e := by
    rw [mul_mul_mul_comm, hcc, ← map_mul, mul_inv_cancel₀ hcE, map_one, mul_one]
  rw [smul_finRat_natCast hinf, smul_map_inv hcc, symplOH_smul, smul_smul, RingHom.map_mul, cA_incA_natCast, hs]

theorem finRat_mem {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hcc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {SS : Finset (HeightOneSpectrum (𝓞 D.host.E))} {c : ℕ} (hc : 0 < c)
    {x' : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c) :
    GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' ((c : D.host.E) • x')) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  have e1 : GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' ((c : D.host.E) • x')) =
      finTens 1 (LinearMap.toMatrix' ((c : D.host.E) • x')) := by ext i j; rfl
  rw [e1]
  exact finTens_mem_latO (one_mem_intAf _)
    (GlobalTheory.AdForm.HalfPairing.toMatrix_mem_latRat hcc hN (natCast_smul_mem_of_halfAO hc hx))

theorem conjHalf_mem {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hcc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (hE : IsIdemSum e SS)
    {c : ℕ} {x' : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c) :
    ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • x')).map fun r => cA D e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  have hno : ∀ PP ∈ SS, Formalism.L2.Col.conjPrime₂ PP ∉ SS := fun PP hPP => conjP_not_mem hE hPP
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE
  have e1 : ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • x')).map fun r => cA D (∑ PP ∈ SS, es PP) * incA D r : WO S T) =
      ∑ PP ∈ SS, ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • x')).map fun r => cA D (es PP) * incA D r : WO S T) := by
    ext i j

    rw [Matrix.map_apply, Matrix.sum_apply, map_sum, Finset.sum_mul]
    rfl
  rw [e1]
  refine sum_mem fun PP hPP => GlobalTheory.AdForm.HalfPairing.conj_comp_mem hcc hN (hes PP hPP) ?_ ?_
  · refine GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨es, fun Q hQ => ?_, (Finset.sum_singleton _ _).symm⟩, (hes PP hPP).1.2.1⟩
    rw [Finset.mem_singleton.1 hQ]
    exact hes PP hPP
  · have h : ((c : D.host.E) ^ (-expS SS (Formalism.L2.Col.conjPrime₂ PP)))⁻¹ • x' ∈
        Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ PP).asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :=
      (Submodule.mem_iInf _).1 hx _
    have hexp : expS SS (Formalism.L2.Col.conjPrime₂ PP) = -1 := by
      unfold expS
      rw [if_neg (hno PP hPP), conjP_conjP, if_pos hPP]
    rw [hexp, neg_neg, zpow_one] at h
    exact h

theorem cocycle_trivial : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ψ (symplOH S T ((LinearMap.toMatrix' x').map fun r => e * incA D r) ((GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r))) = 1 := by
  intro D ψ θ S T δ sc hP e SS hE h2 N N' hN hN' c hc _hodd x' hx
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum hE
  have hinfc : infPart D (cA D e) = 0 := GlobalTheory.PlaceDatum.infPart_cA hinf
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hE
  have hcc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have H := GlobalTheory.HalfCocycle.char_symplOH_idem_conj D ψ θ S T δ sc hP e SS hE h2 N N' hN hN' _ (finRat_mem hP.cc hN hc hx) _
    (conjHalf_mem hP.cc hN hE hx)
  have e1 : ∀ r : D.host.E, (LinearMap.toMatrix' (r • x') : Matrix (Fin T.rank) (Fin S.rank) D.host.E) =
      r • LinearMap.toMatrix' x' := fun r => LinearEquiv.map_smul LinearMap.toMatrix' r x'
  rw [e1, e1, rhs_eq hinf hcc hc] at H
  rw [lhs_eq hinfc hE.2]
  exact H

end GlobalTheory.AdForm.CocycleSS
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.twistedChain_stage_soft_properties : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, SoftQ D := by
  first | exact @GlobalTheory.ChainTw.softQ_all | exact GlobalTheory.ChainTw.softQ_all | (intros; apply GlobalTheory.ChainTw.softQ_all <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

namespace GlobalTheory.FinPl.SelfDualConj

theorem conj_at_place : ∀ (D : D7) (V : HSp D) (L M : Lat V), IsSelfDualC V L → IsSelfDualC V M →
    ∀ x : Pl D, ∃ g ∈ grpAt V (· = x), Moves V g L M (· = x) := by
  intro D V L M hL hM x
  obtain ⟨γ, hγ, h⟩ := GlobalTheory.T.selfDualLattices_single_orbit_tamePlace D V x (latV V L (· = x)) (latV V M (· = x)) (GlobalTheory.FinPl.TamePlaces.tame D x)
    (GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V L x hL) (GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V M x hM)
  exact ⟨γ, hγ, fun y hy => h y hy⟩

end GlobalTheory.FinPl.SelfDualConj
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSaw_scalarForms_continuous_automorphic_central : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → RdX t := by
  first | exact @GlobalTheory.SeeSaw.rdX_of_clsPinD | exact GlobalTheory.SeeSaw.rdX_of_clsPinD | (intros; apply GlobalTheory.SeeSaw.rdX_of_clsPinD <;> assumption)
end
