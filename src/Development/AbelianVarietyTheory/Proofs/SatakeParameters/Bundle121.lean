module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPDivOfUnit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle254
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletion
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle044
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle111
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Tensor
public import Formalism.ConjugateSelfDual.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle113
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.TopSrc

open GlobalTheory.DatumLaw

theorem of_zero {E : Type} [Field E] {n c : ℕ} (hc : c = 0) (r : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (κ : Sp E n ≃ₗ[E] Sp E n)
    (h : ∀ x, r (Loc.inX E n c x) = Loc.inX E n c (κ x)) :
    κ.toLinearMap ∘ₗ LinearMap.funLeft E E (Fin.castAdd c) = LinearMap.funLeft E E (Fin.castAdd c) ∘ₗ r.toLinearMap ∧
      LinearEquiv.det κ = LinearEquiv.det r ∧ Loc.n1Arg r = 0 := by
  subst hc
  have e : ∀ x : Sp E n, Loc.inX E n 0 x = x := fun x => by
    funext l
    rw [CongLevel.inX_apply]
    exact dif_pos l.2
  have hr : r = κ := LinearEquiv.ext fun x => by
    have := h x
    rwa [e, e] at this
  subst hr
  refine ⟨rfl, rfl, ?_⟩
  unfold Loc.n1Arg
  simp

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem phiTop_source (sharp : Bool) {m2 : ℕ} (hm : R.m = m2 + 2) (P : rowSG Pr sel mu) {g : AutY X R (m2 + 1)}
    (hg : g ∈ Jat (Pr := Pr) sharp (m2 + 1) P.1) (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0)) :
    PhiTop Ch mu sharp m2 P.1 (x ∘ₗ g.toLinearMap) * rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      lamRow Ch mu sharp (m2 + 1) P.1 g.toLinearMap * PhiTop Ch mu sharp m2 P.1 x := by
  obtain ⟨a1, a2, a3, a4⟩ := ranks R (j := m2 + 1) (by omega)
  have b1 := rank_X'_eq R
  have b2 : R.r + (m2 + 1) * R.t ≤ R.N R.m - 1 + 0 := by
    rw [b1, add_zero]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  have hb : R.r ≤ R.N R.m - 1 + 0 := by omega
  unfold rhoS
  unfold Jat at hg
  unfold PhiTop lamRow
  generalize R.N R.m - 1 = n at *
  have e1 := fun ψ χ => hm ▸ phiGS_eq (K := X.K) (P := P.1) ψ χ (k₀ := R.k) (rS := R.rS) (r := R.r) (t := R.t) (i := m2 + 1)
    (c' := cOf R (m2 + 1)) (n' := R.N (m2 + 1)) (c := 0) (n := n)
  have e2 := fun ψ χ => hm ▸ phiG_eq (K := X.K) (P := P.1) ψ χ (k₀ := R.k) (r := R.r) (t := R.t) (i := m2 + 1)
    (c' := cOf R (m2 + 1)) (n' := R.N (m2 + 1)) (c := 0) (n := n)
  split_ifs at hg ⊢
  · rw [e1]
    exact phiM_source _ _ (by omega) (by omega) a1 b2 _ inf_le_left
      (fun g hg => levG_of_JGsym (by omega) a4 (by omega) hg) hg x
  · rw [e2, LocE.lamGB, lamGv_eq]
    exact phiM_source _ _ (by omega) (by omega) a1 b2 _ inf_le_left
      (fun g hg => levG_of_JG (by omega) (by omega) hg) hg x
  · exact phiQ_source _ (by omega) a2 a3 hb hg x

theorem phiTop_level : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → L.Ok Ch sel mu cst G m2 → ∀ (b : L.β (m2 + 1)) (P : rowSG Pr sel mu) (κ : GLint X.E (R.N (m2 + 1)) P.1) (c : X.Kˣ), (∀ hP : P.1 ∈ Pr.vGs, ∃ h : redGL _ P.1 κ ∈ (L.levG (m2 + 1) b ⟨P.1, hP⟩).H, c = (L.levG (m2 + 1) b ⟨P.1, hP⟩).lam ⟨_, h⟩) → (∀ hQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K), P.1 ∉ Pr.vGs → ∃ h : κ ∈ (L.levQ (m2 + 1) b ⟨P.1, hQ⟩).H, c = (L.levQ (m2 + 1) b ⟨P.1, hQ⟩).lam ⟨κ, h⟩) → ∀ x : HomE X.E (R.N (m2 + 1)) ((R.N R.m - 1) + 0), PhiTop Ch mu cst.sharp m2 P.1 (x ∘ₗ κ.1.toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) * rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det κ.1 : X.Eˣ) : X.E) = (c : X.K) * PhiTop Ch mu cst.sharp m2 P.1 (x ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hL b P κ c hG hQ x
  have hc : cOf R (m2 + 1) = 0 := by
    have := hL.hm
    unfold cOf
    omega
  have key : ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp (m2 + 1) P.1) (L.h (m2 + 1) b P),
      (∀ x, r (Loc.inX X.E _ (cOf R (m2 + 1)) x) = Loc.inX X.E _ (cOf R (m2 + 1)) (κ.1 x)) ∧
        (c : X.K) = chiInv Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) r := by
    by_cases hP : P.1 ∈ Pr.vGs
    · obtain ⟨h, rfl⟩ := hG hP
      obtain ⟨g, hg, hred⟩ := (hL.grpG (m2 + 1) b ⟨P.1, hP⟩ _).1 h
      have hgi : g ∈ GLint X.E (R.N (m2 + 1)) P.1 := hL.int (m2 + 1) b P hg
      have e : redGL _ P.1 ⟨g, hgi⟩ = redGL _ P.1 κ := redGL_eq _ hred
      have h1 : redGL _ P.1 ((⟨g, hgi⟩ : GLint X.E (R.N (m2 + 1)) P.1)⁻¹ * κ) = 1 := by
        rw [map_mul, map_inv, e, inv_mul_cancel]
      have h2 := CongLevel.cong_mem_prCat X Pr R cst.sharp (m2 + 1) P.1 hP
        (fun a ha h0 => intAt_div_of_redP (qOf_notMem_sq hX hPr hP) ha h0) _ (hL.stabG (m2 + 1) b P hP)
        _ ((⟨g, hgi⟩ : GLint X.E (R.N (m2 + 1)) P.1)⁻¹ * κ).2 fun x hx => by
          rw [redV_redGL _ hx, h1, Units.val_one, Matrix.one_mulVec]
      have h3 : κ.1 ∈ prCat (Pr := Pr) cst.sharp (m2 + 1) P.1 (L.h (m2 + 1) b P) := by
        have := mul_mem hg h2
        rwa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at this
      obtain ⟨r, hr, hrx⟩ := h3
      exact ⟨r, hr, hrx, hL.chrG (m2 + 1) b ⟨P.1, hP⟩ ⟨_, h⟩ κ.1 r hr hrx fun x hx => redV_redGL κ hx⟩
    · have hP' := (@Finset.mem_union _ (Classical.decEq _) _ _ _).1 P.2 |>.resolve_left hP
      obtain ⟨h, rfl⟩ := hQ hP' hP
      have h3 := h
      rw [hL.grpQ, Subgroup.mem_subgroupOf] at h3
      obtain ⟨r, hr, hrx⟩ := h3
      exact ⟨r, hr, hrx, hL.chrQ (m2 + 1) b ⟨P.1, hP'⟩ ⟨_, h⟩ r hr hrx⟩
  obtain ⟨r, hr, hrx, hcr⟩ := key
  rw [hL.last_h] at hr hcr
  have hJ : r ∈ Jat (Pr := Pr) cst.sharp (m2 + 1) P.1 := by simpa using hr.2
  obtain ⟨e1, e2, e3⟩ := of_zero hc r κ.1 hrx
  unfold chiInv at hcr
  rw [e3, hL.cst_ok.psi_int P 0 intAt_zero, inv_one, one_mul, inv_one, one_mul, mul_one] at hcr
  rw [e1, e2, hcr, ← LinearMap.comp_assoc]
  exact phiTop_source Ch sel mu cst.sharp hL.hm P hJ _

end GlobalTheory.TopSrc

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField
open scoped TensorProduct Matrix

namespace GlobalTheory.PlaceComp

section Gen

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def finP : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

def infP : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom

def intA : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

variable {F}

def evF (v : HeightOneSpectrum (𝓞 F)) : Af F ⊗[F] E →+* Fv F v ⊗[F] E :=
  (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)).toRingHom

def ordAt (v : HeightOneSpectrum (𝓞 F)) : Subring (Fv F v ⊗[F] E) :=
  Subring.closure {y | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

def sgT (v : HeightOneSpectrum (𝓞 F)) : Fv F v ⊗[F] E →ₗ[F] Af F ⊗[F] E :=
  TensorProduct.map (GlobalTheory.AutFunCompare.sgV v) LinearMap.id

def IsIdemOf (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E) : Prop :=
  infP F E e = 0 ∧ evF E v (finP F E e) = 1 ∧ ∀ w, w ≠ v → evF E w (finP F E e) = 0

variable {E}

omit [NumberField E] in
theorem evF_sgT_self (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) : evF E v (sgT E v y) = y := by
  classical
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a e =>
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (singleV F v a) ⊗ₜ e = _
    rw [GlobalTheory.AutFunCompare.evalV_singleV, Pi.single_eq_same]

omit [NumberField E] in
theorem evF_sgT_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (y : Fv F v ⊗[F] E) : evF E w (sgT E v y) = 0 := by
  classical
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
  | tmul a e =>
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (singleV F v a) ⊗ₜ e = _
    rw [GlobalTheory.AutFunCompare.evalV_singleV, Pi.single_eq_of_ne h, TensorProduct.zero_tmul]

omit [NumberField E] in
theorem evF_ext {z z' : Af F ⊗[F] E} (h : ∀ v, evF E v z = evF E v z') : z = z' :=
  GlobalTheory.LatticeLocalGlobal.ext_components z z' h

omit [NumberField E] in
theorem evF_finP_incl (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    evF E v (finP F E (inclR (AF F) x)) = inclR (Fv F v) x := by
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (sndA F 1) ⊗ₜ x = (1 : Fv F v) ⊗ₜ x
  rw [map_one, map_one]


omit [NumberField E] in
theorem isIdemOf_algebraMap {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v α = 1)
    (h2 : ∀ w, w ≠ v → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w α = 0) :
    IsIdemOf E v (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 α)) := by
  refine ⟨?_, ?_, fun w hw => ?_⟩
  · show (0 : Ainf F) ⊗ₜ (1 : E) = 0
    exact TensorProduct.zero_tmul _ _
  · show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v α ⊗ₜ (1 : E) = 1
    rw [h1]; rfl
  · show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w α ⊗ₜ (1 : E) = 0
    rw [h2 w hw]; exact TensorProduct.zero_tmul _ _

variable [StarRing E] (hc : CMData F E) (V : HSpace E)

abbrev lamHat (F : Type) [Field F] [NumberField F] [Algebra F E] (V : HSpace E) :
    AddSubgroup (Fin V.rank → Af F ⊗[F] E) :=
  latHat F E {x : Fin V.rank → E | ∑ i, x i • V.frame i ∈ V.L0}

def locMat (v : HeightOneSpectrum (𝓞 F)) : HA (AF F) hc.sig V.gram →* GL (Fin V.rank) (Fv F v ⊗[F] E) :=
  (Formalism.UG.bc (evF E v)).comp ((Formalism.UG.bc (finP F E)).comp (HR (AF F) hc.sig V.gram).subtype)

def Supp (f : AF F ⊗[F] E) (g : HA (AF F) hc.sig V.gram) : Prop :=
  ∀ i j, f * ((HA.mat (AF F) hc.sig V.gram g).1 - 1) i j = ((HA.mat (AF F) hc.sig V.gram g).1 - 1) i j

def IsFin (g : HA (AF F) hc.sig V.gram) : Prop :=
  Formalism.UG.bc (infP F E) (HA.mat (AF F) hc.sig V.gram g) = 1

def Stab (g : HA (AF F) hc.sig V.gram) : Prop :=
  ∀ y, y ∈ lamHat F V ↔ (finMat hc.sig V.gram g).mulVec y ∈ lamHat F V

def DivG (e : AF F ⊗[F] E) (ϖ : E) (d : Fin V.rank → ℤ) (α : HA (AF F) hc.sig V.gram) : Prop :=
  ∃ B : Matrix (Fin V.rank) (Fin V.rank) (Af F ⊗[F] E),
    (∀ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) → (fun a => finP F E e * B.mulVec z a) ∈ lamHat F V) ∧
    (∀ y ∈ lamHat F V, ∃ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) ∧
      (fun a => finP F E e * y a) = fun a => finP F E e * B.mulVec z a) ∧
    (∀ y ∈ lamHat F V, ∃ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) ∧
      (fun a => finP F E e * (finMat hc.sig V.gram α).mulVec y a) =
        fun a => finP F E e * B.mulVec (fun i => finP F E (inclR (AF F) (ϖ ^ d i)) * z i) a) ∧
    (∀ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) → ∃ y ∈ lamHat F V,
      (fun a => finP F E e * (finMat hc.sig V.gram α).mulVec y a) =
        fun a => finP F E e * B.mulVec (fun i => finP F E (inclR (AF F) (ϖ ^ d i)) * z i) a)

theorem locMat_val (v : HeightOneSpectrum (𝓞 F)) (g : HA (AF F) hc.sig V.gram) :
    (locMat hc V v g).1 = (finMat hc.sig V.gram g).map (evF E v) := rfl

theorem locMat_mem (v : HeightOneSpectrum (𝓞 F)) (g : HA (AF F) hc.sig V.gram) :
    locMat hc V v g ∈ HR (Fv F v) hc.sig V.gram :=
  (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projLoc hc V v (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projFin hc V g)).2

theorem mem_lamHat_iff (y : Fin V.rank → Af F ⊗[F] E) :
    y ∈ lamHat F V ↔ ∀ v, (fun i => evF E v (y i)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v :=
  GlobalTheory.LatticeLocalGlobal.mem_latHat_iff F E V y

def IsFrameAt (v : HeightOneSpectrum (𝓞 F)) (h : GL (Fin V.rank) (Fv F v ⊗[F] E)) : Prop :=
  ∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v ↔ ∀ i, (h⁻¹).1.mulVec x i ∈ ordAt E v

end Gen

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing
open GlobalTheory.SelfDualGenus

theorem mem_ordAt_iff (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (z : LocAlg v) :
    z ∈ ordAt E v ↔ z ∈ locOrder v := by
  constructor
  · intro hz
    refine (Subring.closure_le (t := (locOrder v).toSubring)).2 ?_ hz
    rintro _ ⟨a, ha, x, rfl⟩
    have := mul_mem ((locOrder v).algebraMap_mem ⟨a, ha⟩) (locEmb_mem_locOrder v x)
    have e : algebraMap (v.adicCompletionIntegers (maximalRealSubfield E)) (LocAlg v) ⟨a, ha⟩ * locEmb v (x : E) =
        a ⊗ₜ (x : E) := by
      show (a ⊗ₜ 1 : LocAlg v) * (1 ⊗ₜ (x : E)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e] at this
    exact this
  · intro hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Subring.subset_closure ⟨1, one_mem _, a, rfl⟩
    | algebraMap r => exact Subring.subset_closure ⟨r, r.2, 1, rfl⟩
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy

theorem unramified (hc : CMData (maximalRealSubfield E) E) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
  Formalism.L2.Pj.unramBridge_holds E fun P hP => by
    obtain ⟨θ, t, e1, e2⟩ := hc.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) θ = t :=
      RingOfIntegers.ext e1.symm
    rwa [this]

theorem exists_orthonormal (hc : CMData (maximalRealSubfield E) E) (V : HSpace E)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ h : GL (Fin V.rank) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E), IsFrameAt V v h ∧
      Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) hc.sig) h.1 * JR (Fv (maximalRealSubfield E) v) V.gram * h.1 = 1 := by
  haveI := unramified hc
  have hG : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (V.gramᵀ a b) = V.gramᵀ b a :=
    fun a b => V.herm.eq (V.frame b) (V.frame a)
  have hd : V.gramᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero
  obtain ⟨h, h1, h2⟩ := exists_orthonormal_frame hG hd
    (GlobalTheory.LocalConjugacy.isLattice_coordLat V V.L0 V.standardTuple_isLattice)
    (GlobalTheory.LocalConjugacy.selfDual_coordLat V V.L0 V.baseLattice_isUnimodular) v
  refine ⟨h, fun x => (GlobalTheory.LocalConjugacy.mem_latLoc_iff V v x).trans ((h2 x).trans
    (forall_congr' fun i => (mem_ordAt_iff v _).symm)), ?_⟩
  have h3 := congrArg Matrix.transpose h1
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
    Matrix.transpose_one] at h3
  exact h3

end CM

end GlobalTheory.PlaceComp
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt

noncomputable section

namespace GlobalTheory.TwU

theorem map_mem_homLat_of_mem_YYl : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : D.host.E →+* Qq) (hA : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E)) (h1 : ∀ x : 𝓞 D.host.E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) {k k' : ℕ} (N : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin k' → D.host.E)) (a : Matrix (Fin k) (Fin k) Qq) (b : Matrix (Fin k') (Fin k') Qq) (hNa : Submodule.span W ((fun x i => ρ (x i)) '' (N : Set (Fin k → D.host.E))) = colSpan W a) (hNb : Submodule.span W ((fun x i => ρ (x i)) '' (N' : Set (Fin k' → D.host.E))) = colSpan W b), ∀ A ∈ TaylorLogMetric.YYl D N N', A.map ρ ∈ homLat W (colSpan W a) (colSpan W b) := by
  intro D P W Qq _ _ _ _ _ _ p hp ρ hA h1 k k' N N' a b hNa hNb

  have hsc : ∀ (c : D.host.E) (M : Matrix (Fin k') (Fin k) D.host.E), (∃ y : W, ρ c = algebraMap W Qq y) →
      M.map ρ ∈ homLat W (colSpan W a) (colSpan W b) → (c • M).map ρ ∈ homLat W (colSpan W a) (colSpan W b) := by
    rintro c M ⟨y, hy⟩ hM z hz
    have e : (c • M).map ρ = y • M.map ρ := by
      ext i j
      simp [Matrix.map_apply, map_mul, hy, Algebra.smul_def]
    rw [e, Matrix.smul_mulVec]
    exact (colSpan W b).smul_mem y (hM z hz)
  have hO : ∀ c : 𝓞 D.host.E, ∃ y : W, ρ (c : D.host.E) = algebraMap W Qq y := fun c =>
    (h1 c).imp fun y hy => hy.1

  have hAA : ∀ x ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ y : W, ρ x = algebraMap W Qq y := by
    intro x hx
    have hx' : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) :=
      ⟨1, P.asIdeal.primeCompl.one_mem, by simpa using hx⟩
    rw [hA] at hx'
    obtain ⟨s, hs, hsx⟩ := hx'
    obtain ⟨t, ht⟩ := Submodule.mem_one.1 hsx
    obtain ⟨ys, hys, hsP⟩ := h1 s
    obtain ⟨yt, hyt⟩ := hO t
    have hu : IsUnit ys := by
      have hmax : IsLocalRing.maximalIdeal W = Ideal.span {(p : W)} :=
        (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hp
      by_contra hn
      have : ys ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal ys).2 hn
      rw [hmax, Ideal.mem_span_singleton] at this
      exact hs (hsP.2 this)
    refine ⟨hu.unit⁻¹ * yt, ?_⟩
    have e1 : ρ (algebraMap (𝓞 D.host.E) D.host.E t) = ρ (s : D.host.E) * ρ x := by
      rw [ht, Algebra.smul_def, map_mul]
    have e2 : algebraMap W Qq ys ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective W Qq)]
      exact hu.ne_zero
    rw [map_mul, ← hyt]
    change _ = _ * ρ (t : D.host.E)
    rw [show ((t : D.host.E)) = algebraMap (𝓞 D.host.E) D.host.E t from rfl, e1, hys, ← mul_assoc, ← map_mul,
      IsUnit.val_inv_mul, map_one, one_mul]

  have hHom : ∀ A ∈ TaylorLogMetric.homL D N N', A.map ρ ∈ homLat W (colSpan W a) (colSpan W b) := by
    intro A hA'
    induction hA' using Submodule.span_induction with
    | mem A hA0 =>
      intro z hz
      rw [← hNa] at hz
      rw [← hNb]
      induction hz using Submodule.span_induction with
      | mem z hz0 =>
        obtain ⟨x, hx, rfl⟩ := hz0
        refine Submodule.subset_span ⟨A *ᵥ x, hA0 x hx, ?_⟩
        funext i

        simp [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
      | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
      | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hz hz'
      | smul c z _ hz => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c hz
    | zero => rw [Matrix.map_zero _ (map_zero ρ)]; exact Submodule.zero_mem _
    | add A B _ _ hA hB => rw [Matrix.map_add _ (map_add ρ)]; exact Submodule.add_mem _ hA hB
    | smul c A _ hA => exact hsc (c : D.host.E) A (hO c) hA
  intro A hA'
  induction hA' using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨c, hc, A, hA0, rfl⟩ := hB
    exact hsc c A (hAA c hc) (hHom A hA0)
  | zero => rw [Matrix.map_zero _ (map_zero ρ)]; exact Submodule.zero_mem _
  | add A B _ _ hA hB => rw [Matrix.map_add _ (map_add ρ)]; exact Submodule.add_mem _ hA hB
  | smul c A _ hA => exact hsc (c : D.host.E) A (hO c) hA

end GlobalTheory.TwU

end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

theorem GlobalTheory.DFrame.pairedBlock_diag : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (X : Fields) (s : Seam D X) (L : PeriodPair) (sc : ℝ) (n : Bool × HH D → ℕ) (N N' : ℕ) (a : ∀ z, Fin (n z) → D.host.E) (cκ : Bool × HH D → ℂ_[p]) (r : ∀ z, Fin (n z) → ℂ_[p]) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (σ σ' : Bool × HH D → 𝓞 D.host.E) (th : ℂ_[p]), ‖th‖ ≤ 1 → (∀ A B : Matrix (Fin N') (Fin N) D.host.E, ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' sc) (GlobalTheory.DFrame.vecF D s A) (GlobalTheory.DFrame.vecF D s B)) = ∑ z : Bool × HH D, GlobalTheory.DFrame.rho D ι z (∑ i, ∑ k, A i k * D.host.conj (B i k))) → (∀ τ ρ : Bool × HH D, ρ ≠ τ → ∀ α' : (Σ z : Bool × HH D, Fin (n z)), ∑ α, GlobalTheory.DFrame.gc D cκ r τ α * GlobalTheory.DFrame.rho D ι ρ (a α.1 α.2 * D.host.conj (a α'.1 α'.2)) = 0) → (∀ t, ‖GlobalTheory.DFrame.uu D ι cκ r a t‖ ≤ 1) → (∀ (t : HH D) (a₁ a₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ l, ∑ l₂, GlobalTheory.DFrame.pc D ι σ (false, t) l a₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ j, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j)) * GlobalTheory.DFrame.pc D ι σ (true, t) l₂ a₂ = (if a₁ = a₂ then 1 else 0) + th * e) → (∀ (t : HH D) (b₁ b₂ : Fin N'), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ r₁, ∑ r₂, GlobalTheory.DFrame.pc D ι σ' (false, t) r₁ b₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ i, GlobalTheory.DFrame.colR D P' σ' r₁ i * D.host.conj (GlobalTheory.DFrame.colR D P' σ' r₂ i)) * GlobalTheory.DFrame.pc D ι σ' (true, t) r₂ b₂ = (if b₁ = b₂ then 1 else 0) + th * e) → ∀ (t : HH D) (ab ab' : Fin N × Fin N'), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ j, ∑ k, GlobalTheory.DFrame.coef D ι cκ r σ σ' j ((false, t), ab) * ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' sc) (GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' j)) (GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' k))) * GlobalTheory.DFrame.coef D ι cκ r σ σ' k ((true, t), ab') = (if ab = ab' then GlobalTheory.DFrame.uu D ι cκ r a t else 0) + th * e := by
  intro D p _ ι X s L sc n N N' a cκ r P P' σ σ' th hth hOK hvan hu hL hR t ab ab'
  obtain ⟨e, he, hE⟩ := Formalism.L2.Th1.GD.tripleTensorAlmostOrthonormal ℂ_[p] D.host.E (HH D) (GlobalTheory.DFrame.rho D ι)
    (Σ z : Bool × HH D, Fin (n z)) ((Bool × HH D) × Fin N) ((Bool × HH D) × Fin N')
    (fun α α' => a α.1 α.2 * D.host.conj (a α'.1 α'.2))
    (fun (l l₂ : (Bool × HH D) × Fin N) => ∑ j : Fin N, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j))
    (fun (q q₂ : (Bool × HH D) × Fin N') => ∑ i : Fin N', GlobalTheory.DFrame.colR D P' σ' q i * D.host.conj (GlobalTheory.DFrame.colR D P' σ' q₂ i))
    N N' (GlobalTheory.DFrame.gc D cκ r) (GlobalTheory.DFrame.pc D ι σ) (GlobalTheory.DFrame.pc D ι σ') th
    (GlobalTheory.DFrame.uu D ι cκ r a) hth hvan (fun _ => rfl) hu hL hR t ab ab'
  refine ⟨e, he, ?_⟩
  rw [← hE]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [hOK]
  unfold GlobalTheory.DFrame.coef
  congr 2
  refine Finset.sum_congr rfl (fun z _ => ?_)
  congr 1
  simp only [GlobalTheory.DFrame.mat, Matrix.of_apply, map_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.exists_normV_eq_normV_under_pow : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M)), ∃ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f := by
  first | exact @GlobalTheory.AboveL.ResDeg.normV_eq_under_pow | exact GlobalTheory.AboveL.ResDeg.normV_eq_under_pow | (intros; apply GlobalTheory.AboveL.ResDeg.normV_eq_under_pow <;> assumption)
end

section

open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

theorem _root_.GlobalTheory.T.adelicInner_doubleCosetOp_adjoint : ∀ {G Γ W I : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Fintype I] (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J L : Subgroup G) (χ : J →* ℂˣ) (y : I → G) (x : G) (A A' : Finset G), (∀ γ u u', inner ℂ (ρ γ u) (ρ γ u') = inner ℂ u u') → (∀ k, ‖(χ k : ℂ)‖ = 1) → IsReps ι J y → (∀ i, Finite (stab ι J (y i))) → (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l) → (∀ k : J, (k : G) ∈ L → χ k = 1) → (∀ a ∈ A, a ∈ L) → (∀ a ∈ A', a ∈ L) → IsDC J x A → IsDC J x⁻¹ A' → ∀ F ∈ AdForms ι ρ J χ, ∀ F' ∈ AdForms ι ρ J χ, adInner ι J y (dcOp A F) F' = adInner ι J y F (dcOp A' F') := by
  first | exact @GlobalTheory.adInner_dcOp_adjoint | exact GlobalTheory.adInner_dcOp_adjoint | (intros; apply GlobalTheory.adInner_dcOp_adjoint <;> assumption)
end
