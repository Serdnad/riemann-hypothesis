module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle065
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle113
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle114
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeckeLawPointKernelOfCoefficientKernel
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle112
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CardStabilizerForgetFr
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa

@[expose] public section

section

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

theorem _root_.GlobalTheory.T.quotient_integration_formula_discrete_subgroup_left : DiscreteClause := by
  first | exact @GlobalTheory.QuotDiscrete.discreteClause | exact GlobalTheory.QuotDiscrete.discreteClause | (intros; apply GlobalTheory.QuotDiscrete.discreteClause <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure MeasureTheory

namespace GlobalTheory.RationalStabiliserDomains

theorem isDiscreteWithDomains_inf_subgroupOf {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ S : Subgroup G) [Countable Γ] [DiscreteTopology Γ] :
    IsDiscreteWithDomains ((Γ ⊓ S).subgroupOf S) := by
  let f : (Γ ⊓ S).subgroupOf S → Γ := fun g => ⟨g.1.1, g.2.1⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : Γ => (z : G)) h))
  have hc : Continuous f :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have : Countable ((Γ ⊓ S).subgroupOf S) := hf.countable
  have : DiscreteTopology ((Γ ⊓ S).subgroupOf S) := DiscreteTopology.of_continuous_injective hc hf
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology (S : Set G)
  exact GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_of_discrete _

theorem isDiscreteWithDomains_HstabFin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → IsDiscreteWithDomains (HstabFin (AF F) σ J x) := by
  intro F E _ _ _ _ _ σ _ M J _ x _
  have := (GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E σ M J).2.1
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J
  have h := GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts' F E σ M J
  have := h.1
  have := h.2.1
  exact isDiscreteWithDomains_inf_subgroupOf (ratPts (AF F) σ J) (Hstab (AF F) σ J x)

end GlobalTheory.RationalStabiliserDomains
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure

theorem _root_.GlobalTheory.T.unitaryRationalPoints_countable_discrete_fundDomains_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsDiscreteWithDomains (ratPts (AF F) σ J) := by
  first | exact @GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts | exact GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts | (intros; apply GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.TilClass

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
open GlobalTheory.TopStep (sumE prH extI redGL)

section Points

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N n : ℕ} (hN : N = n + 1)
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

variable (hconj : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
  (hbig : 2 ^ Module.finrank ℚ E < ∏ P ∈ ST, Ideal.absNorm P.asIdeal) {pi : 𝓞 E}
  (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal)
include hconj hbig hT hG

end Points

section Size

variable {X : Fields} {Pr : Primes X}

end Size

section Branch

theorem isBlock_of_mulVec {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1) {A' : Matrix (Fin N) (Fin N) E}
    {A : Matrix (Fin n) (Fin n) E} (h1 : ∀ x, iniH hN (A'.mulVec x) = A.mulVec (iniH hN x))
    (h2 : ∀ x, A'.mulVec x (Br.iL hN) = x (Br.iL hN)) : BranchFormula.IsBlock hN A' A 1 := by
  have hne : ∀ a : Fin n, Br.iC hN a ≠ Br.iL hN := fun a h => absurd (congrArg Fin.val h) a.2.ne
  have hinj : Function.Injective (Br.iC hN) := fun a b h => Fin.ext (congrArg Fin.val h :)
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · have h := congrFun (h1 (Pi.single (Br.iC hN b) 1)) a
    have e : iniH hN (Pi.single (Br.iC hN b) (1 : E)) = Pi.single b 1 := funext fun i => by
      simp only [iniH, Pi.single_apply, hinj.eq_iff]
    rw [e, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    exact h
  · have h := congrFun (h1 (Pi.single (Br.iL hN) 1)) a
    have e : iniH hN (Pi.single (Br.iL hN) (1 : E)) = 0 := funext fun i => Pi.single_eq_of_ne (hne i) _
    rw [e, Matrix.mulVec_single_one, Matrix.mulVec_zero] at h
    exact h
  · have h := h2 (Pi.single (Br.iC hN a) 1)
    rw [Matrix.mulVec_single_one, Pi.single_eq_of_ne (hne a).symm] at h
    exact h
  · have h := h2 (Pi.single (Br.iL hN) 1)
    rw [Matrix.mulVec_single_one, Pi.single_eq_same] at h
    exact h

theorem brStd_rhoVr {E K ι : Type} [Field E] [Field K] [CharZero K] [Fintype ι] {N n : ℕ} (hN : N = n + 1) (e : ι → E →+* K)
    {lam : ι → DomWeight N} {sg : ι → DomWeight n} (hI : ∀ τ, Br.Interlace hN (lam τ) (sg τ))
    (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) {γ' : GL (Fin N) E} {γ : GL (Fin n) E}
    (h : BranchFormula.IsBlock hN ((γ'⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)
      ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) 1) (G : VV K lam) :
    Br.brStd hN lam sg (rhoVr e lam γ' G) = rhoVr e sg γ (Br.brStd hN lam sg G) := by
  refine BranchFormula.equivariance K ι N n hN lam sg hI hS (invTrK (embGL e γ)) (invTrK (embGL e γ')) (fun τ => ?_) G
  have e1 : ∀ {m : ℕ} (g : GL (Fin m) E) (a b : Fin m), ((invTrK (embGL e g) τ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) a b =
      e τ (((g⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) b a) := fun g a b => rfl
  simp only [e1]
  refine ⟨fun a b => by rw [h.1], fun a => ⟨by rw [(h.2.1 a).2, map_zero], by rw [(h.2.1 a).1, map_zero]⟩, by rw [h.2.2, map_one]⟩

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ} (lam : ι → DomWeight n)

theorem mem_ValC_iff (f : Fr emb σ n → ℂ) :
    f ∈ ValC (Gr emb σ n) lam ↔ ∃ F : VV ℂ lam, fnOf (Gr emb σ n) (shiftOf lam) 1 F.1 = f := by
  have e : ∀ F : VV ℂ lam, evV (embAt σ emb) (1 : Matrix (Fin n) (Fin n) E) lam (RingHom.id ℂ) F =
      fnOf (Gr emb σ n) (shiftOf lam) 1 F.1 := fun F => by
    rw [evV_apply, MvPolynomial.map_id]
    rfl
  constructor
  · intro hf
    have h : f ∈ Submodule.span ℂ (Set.range (evV (embAt σ emb) (1 : Matrix (Fin n) (Fin n) E) lam (RingHom.id ℂ))) := by
      rw [span_evV]
      exact hf
    rw [← LinearMap.coe_range, Submodule.span_eq] at h
    obtain ⟨F, rfl⟩ := h
    exact ⟨F, (e F).symm⟩
  · rintro ⟨F, rfl⟩
    rw [← e]
    exact evV_mem_ValC _ _ _ _ F

theorem trFr_fnOf (γ : GL (Fin n) E) (c : Kˣ) (F : VV ℂ lam) :
    trFr emb σ γ c (fnOf (Gr emb σ n) (shiftOf lam) 1 F.1) =
      σ c • fnOf (Gr emb σ n) (shiftOf lam) 1 (rhoVr (embAt σ emb) lam γ F).1 := by
  funext y
  rw [trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  have h := evV_rhoVr_tr (embAt σ emb) (1 : Matrix (Fin n) (Fin n) E) lam (RingHom.id ℂ) γ F y (frMul emb σ γ⁻¹ y) fun τ =>
    (congrFun (congrArg Subtype.val ((frEquiv emb σ γ).apply_symm_apply y)) τ).symm
  rw [evV_apply, evV_apply, MvPolynomial.map_id, MvPolynomial.map_id] at h
  exact h.symm

theorem polOf_fnOf_one (sh : ι → ℤ) (F : Pol ℂ ι n) :
    polOf (Gr emb σ n) sh (fr0 emb σ n) (fnOf (Gr emb σ n) sh 1 F) = F := by
  have e : (fun τ => ((fr0 emb σ n).1 τ)⁻¹) = 1 := funext fun τ => inv_one
  have h := polOf_fnOf (Gr emb σ n) sh (fr0 emb σ n) F
  rwa [e] at h

end Branch

section Period

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
  {I : ChainIn E K ι R} (Q : PerIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R)

variable {Q}

end Period

section Levels

variable {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) {N n : ℕ} (hN : N = n + 1)
  {Q : Finset (HeightOneSpectrum (𝓞 X.E))} (hQ : ∀ P : Q, Pr.piT u ∉ P.1.asIdeal)
  {Λ : LevFam X.E X.K N Pr.vGs} {Θ : LevQFam X.E X.K N Q} {Λ' : LevFam X.E X.K n Pr.vGs} {Θ' : LevQFam X.E X.K n Q}
include hX hPr hQ

variable (hΛ : ∀ h, extGH hN h ∈ Λ.grp ↔ h ∈ Λ'.grp) (hΘ : ∀ c, extQ X.E hN Q c ∈ Θ.grp ↔ c ∈ Θ'.grp)
include hΛ hΘ

end Levels

section Lattices

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (P : LevFam X.E X.K R.r Pr.vGs)

variable (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word)
  (rho : ∀ i (b : Idx sel mu L i), (stepAt sel mu cst L Tp u i).D b → ℂ)
  (rho' : ∀ i (b : Idx sel mu L (i + 1)), (stepAt sel mu cst L Tp u (i + 1)).D b → ℂ) (cD : X.Tau → ℂ)
  (Th : ∀ i (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)), (stepAt sel mu cst L Tp u i).D b →
    (stepAt sel mu cst L Tp u (i + 1)).D b' → Formalism.L2.Ker.VCx X.Tau (R.N i) (R.N (i + 1)) → ℂ)

variable {W Ch sel mu cst L P Tp u rho rho' cD Th} {Q : PerIn (chainAt sel mu cst L Tp u rho rho' cD Th)}

end Lattices

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (P : LevFam X.E X.K R.r Pr.vGs)

end Main

section Top

open GlobalTheory.TopStep (TilOk tilTop tilEl topLevG topLevQ topGSD evTop TopDepth inQ)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {P : LevFam X.E X.K R.r Pr.vGs} {u : Pr.Word}

theorem brC_rho (hW : W.Ok) (γ : UF X.E (R.N R.m - 1)) (x : VV X.K (W.lamTrue u R.m)) :
    brC W u (rhoVr X.emb (W.lamTrue u R.m) (ufGL X.E _ (extUH (N_m_succ R) γ)) x) =
      rhoVr X.emb W.sgTrue (ufGL X.E _ γ) (brC W u x) := by
  have h := brStd_rhoVr (N_m_succ R) X.emb (fun τ => (BranchMembers.members X _ R W hW u τ).1)
    (fun τ => (BranchMembers.members X _ R W hW u τ).2) (γ' := ufGL X.E _ (extUH (N_m_succ R) γ)) (γ := ufGL X.E _ γ) (by
      have e : ∀ y, ((ufGL X.E _ (extUH (N_m_succ R) γ⁻¹) : GL _ _) : Matrix _ _ X.E).mulVec y =
          sumE (N_m_succ R) (γ⁻¹).1 1 y := fun y => by
        rw [← TopStep.extUH_val]
        exact toGLm_mulVec _ y
      rw [← map_inv, ← map_inv, ← map_inv]
      refine isBlock_of_mulVec _ (fun y => ?_) fun y => ?_
      · rw [e]
        exact (TopStep.prH_sumE _ _ _ y).trans (toGLm_mulVec _ _).symm
      · rw [e, TopStep.sumE_last, Units.val_one, one_mul]) x
  rw [brC, Br.brAt, LinearMap.smul_apply, LinearMap.smul_apply, h, map_smul]

end Top

end GlobalTheory.TilClass
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem _root_.GlobalTheory.T.conjugatePrimeBound_pointKernel_of_coefficientKernel : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (Co : M.Coord) (Co' : M'.Coord) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Co.Ok → Co'.Ok → R.ValIs Co → R'.ValIs Co' → Built.Dat.KerBar k → K.IntBar Co Co' := by
  first | exact @GlobalTheory.LvT.Built.BarPass.intBar_of_kerBar | exact GlobalTheory.LvT.Built.BarPass.intBar_of_kerBar | (intros; apply GlobalTheory.LvT.Built.BarPass.intBar_of_kerBar <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem _root_.GlobalTheory.T.dilateLaw_pointKernel_of_coefficientKernel : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Built.Dat.KerDil k → K.DilLaw := by
  first | exact @GlobalTheory.LvT.Built.DilPass.dilLaw_of_kerDil | exact GlobalTheory.LvT.Built.DilPass.dilLaw_of_kerDil | (intros; apply GlobalTheory.LvT.Built.DilPass.dilLaw_of_kerDil <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem _root_.GlobalTheory.T.exists_pointKernel_realised_models : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) , Built.Dat.KerEq k → ∃ K : KerPt M M', K.TgtEq ∧ Built.Dat.KerIs R R' K k := by
  first | exact @GlobalTheory.LvT.Built.KerExt.exists_kerPt | exact GlobalTheory.LvT.Built.KerExt.exists_kerPt | (intros; apply GlobalTheory.LvT.Built.KerExt.exists_kerPt <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem _root_.GlobalTheory.T.heckeLaw_pointKernel_of_coefficientKernel : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Built.Dat.KerUK k → K.UKLaw := by
  first | exact @GlobalTheory.LvT.Built.UK.ukLaw_of_kerUK | exact GlobalTheory.LvT.Built.UK.ukLaw_of_kerUK | (intros; apply GlobalTheory.LvT.Built.UK.ukLaw_of_kerUK <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

namespace GlobalTheory.SplitOfSquare

private theorem valued_v_algebraMap_adicCompletion_foundation {F : Type} [Field F] [NumberField F]
    (u : HeightOneSpectrum (𝓞 F)) (x : F) :
    Valued.v (algebraMap F (u.adicCompletion F) x) = u.valuation F x :=
  u.valuedAdicCompletion_eq_valuation' x

theorem exists_valuation_lt_one {F : Type} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)) (a : F) (ha : a ≠ 0)
    (h : IsSquare (algebraMap F (u.adicCompletion F) a)) : ∃ c : F, u.valuation F (1 / 4 - c ^ 2 * a) < 1 := by
  obtain ⟨s, hs⟩ := h
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply ha
    simpa using hs
  obtain ⟨π, hπ⟩ := u.valuation_exists_uniformizer F
  have hπ1 : u.valuation F π < 1 := by
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  set h2 : u.adicCompletion F := algebraMap F (u.adicCompletion F) 2⁻¹ with hh2
  set p : u.adicCompletion F := algebraMap F (u.adicCompletion F) π with hp
  have hp0 : p ≠ 0 := (map_ne_zero _).mpr hπ0
  have hvp : Valued.v p < 1 := by rw [hp, valued_v_algebraMap_adicCompletion_foundation]; exact hπ1
  have hI := Valued.isOpen_integer (u.adicCompletion F)
  have hcont : Continuous (fun y : u.adicCompletion F => (y * s - h2) * p⁻¹) :=
    ((continuous_id.mul continuous_const).sub continuous_const).mul continuous_const
  obtain ⟨c, hc⟩ := (u.denseRange_algebraMap F).exists_mem_open (hI.preimage hcont) ⟨h2 * s⁻¹, by
    simp only [Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff]
    rw [mul_assoc, inv_mul_cancel₀ hs0, mul_one, sub_self, zero_mul, map_zero]
    exact zero_le⟩
  refine ⟨c, ?_⟩
  simp only [Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff] at hc
  set y := algebraMap F (u.adicCompletion F) c
  set z := y * s - h2 with hz_def
  have hz : Valued.v z < 1 := by
    calc Valued.v z = Valued.v (z * p⁻¹) * Valued.v p := by
          rw [← map_mul, inv_mul_cancel_right₀ hp0]
      _ ≤ 1 * Valued.v p := by gcongr
      _ < 1 := by rw [one_mul]; exact hvp
  have hhalf : h2 + h2 = 1 := by
    rw [hh2, ← map_add (f := _), ← map_one (algebraMap F (u.adicCompletion F))]
    congr 1
    norm_num
  have hkey : algebraMap F (u.adicCompletion F) (1 / 4 - c ^ 2 * a) = -z * (1 + z) := by
    have e1 : (1 / 4 : F) = 2⁻¹ * 2⁻¹ := by norm_num
    rw [e1, map_sub, map_mul, map_mul, map_pow, hs, ← hh2]
    rw [hz_def]
    linear_combination (h2 - y * s) * hhalf
  rw [← valued_v_algebraMap_adicCompletion_foundation, hkey]
  have h1z : Valued.v (1 + z) ≤ 1 := by
    calc Valued.v (1 + z) ≤ max (Valued.v (1 : u.adicCompletion F)) (Valued.v z) :=
          Valuation.map_add _ _ _
      _ ≤ 1 := by rw [map_one]; exact max_le le_rfl hz.le
  calc Valued.v (-z * (1 + z)) = Valued.v z * Valued.v (1 + z) := by
        rw [map_mul, Valuation.map_neg]
    _ ≤ Valued.v z * 1 := by gcongr
    _ < 1 := by rw [mul_one]; exact hz

theorem valuation_complexConj_of_not_split {L : Type} [Field L] [NumberField L] [IsCMField L]
    (w : HeightOneSpectrum (𝓞 L)) (hw : ¬ IsSplitAt w) (y : L) :
    w.valuation L (IsCMField.complexConj L y) = w.valuation L y := by
  set σ : L ≃+* L := (IsCMField.complexConj L).toRingEquiv with hσ
  have hne : w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ) ≠ ⊥ := by
    intro hbot
    apply w.ne_bot
    rw [eq_bot_iff] at hbot ⊢
    intro x hx
    have hx' : (RingOfIntegers.mapRingEquiv σ).symm x ∈
        w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ) := by
      rw [Ideal.mem_comap, RingEquiv.apply_symm_apply]
      exact hx
    have h0 := hbot hx'
    rw [Ideal.mem_bot] at h0 ⊢
    simpa using h0
  obtain ⟨w', hw'⟩ : ∃ w' : HeightOneSpectrum (𝓞 L),
      w'.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ) :=
    ⟨⟨_, Ideal.comap_isPrime _ _, hne⟩, rfl⟩
  have hfix : ∀ x : 𝓞 (maximalRealSubfield L),
      RingOfIntegers.mapRingEquiv σ (algebraMap _ (𝓞 L) x) = algebraMap _ (𝓞 L) x := by
    intro x
    apply RingOfIntegers.ext
    rw [RingOfIntegers.mapRingEquiv_apply]
    have hx : ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) x : 𝓞 L) : L) =
        algebraMap (maximalRealSubfield L) L (x : maximalRealSubfield L) := rfl
    rw [hx]
    exact (IsCMField.complexConj L).commutes _
  have hsame : w' = w := by
    by_contra hne'
    apply hw
    refine ⟨w', hne', ?_⟩
    ext x
    simp only [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, hw', hfix]
  have key := GlobalTheory.QNorm.valuation_of_eq_comap σ w w' hw' y
  rw [hsame] at key
  exact key.symm

theorem isSplitAt_of_isSquare : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : maximalRealSubfield L) (δ : L), δ ^ 2 = a → δ ∉ maximalRealSubfield L → ∀ w : HeightOneSpectrum (𝓞 L), IsSquare (algebraMap (maximalRealSubfield L) ((w.under (𝓞 (maximalRealSubfield L))).adicCompletion (maximalRealSubfield L)) a) → IsSplitAt w := by
  intro L _ _ _ a δ hδ hδL w hsq
  by_contra hw
  set u := w.under (𝓞 (maximalRealSubfield L)) with hu
  have ha : a ≠ 0 := by
    rintro rfl
    apply hδL
    have h0 : δ = 0 := by simpa using hδ
    rw [h0]
    exact zero_mem _
  obtain ⟨c, hc⟩ := exists_valuation_lt_one u a ha hsq
  have hconj : IsCMField.complexConj L δ = -δ := by
    have h1 : (IsCMField.complexConj L δ) ^ 2 = δ ^ 2 := by
      rw [← map_pow, hδ, IsCMField.complexConj_apply_eq_self]
    have h2 : IsCMField.complexConj L δ ≠ δ := fun h =>
      hδL ((IsCMField.complexConj_eq_self_iff L δ).mp h)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
    · exact absurd h h2
    · exact h
  set x : L := 2⁻¹ + (c : L) * δ with hx
  have hcc : IsCMField.complexConj L (c : L) = c := IsCMField.complexConj_apply_eq_self L c
  have hx' : IsCMField.complexConj L x = 2⁻¹ - (c : L) * δ := by
    rw [hx, map_add (f := _), map_mul, hcc, hconj, map_inv₀, map_ofNat]
    ring
  have hsum : x + IsCMField.complexConj L x = 1 := by
    rw [hx', hx]
    ring
  have hprod : x * IsCMField.complexConj L x =
      algebraMap (maximalRealSubfield L) L (1 / 4 - c ^ 2 * a) := by
    rw [hx', hx]
    simp only [map_sub, map_mul, map_pow, map_div₀, map_one, map_ofNat]
    change _ = 1 / 4 - (c : L) ^ 2 * (a : L)
    linear_combination (-(c : L) ^ 2) * hδ
  have : w.asIdeal.LiesOver u.asIdeal := ⟨rfl⟩
  have hlt : w.valuation L (x * IsCMField.complexConj L x) < 1 := by
    rw [hprod, ← HeightOneSpectrum.valuation_liesOver L u w]
    exact pow_lt_one₀ zero_le hc
      (Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal u.ne_bot).ne'
  have heq := valuation_complexConj_of_not_split w hw x
  rw [map_mul, heq] at hlt
  have hx1 : w.valuation L x < 1 := by
    by_contra hge
    push Not at hge
    exact absurd hlt (not_lt.mpr (one_le_mul hge hge))
  have hadd := Valuation.map_add (w.valuation L) x (IsCMField.complexConj L x)
  rw [hsum, map_one, heq, max_self] at hadd
  exact absurd (lt_of_le_of_lt hadd hx1) (lt_irrefl 1)

end GlobalTheory.SplitOfSquare
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

theorem _root_.GlobalTheory.T.weylModule_simple_closedLowestAlcove : GlobalTheory.Published.InducedSimpleLowestAlcove := by
  first | exact @GlobalTheory.Alc.inducedSimpleLowestAlcove | exact GlobalTheory.Alc.inducedSimpleLowestAlcove | (intros; apply GlobalTheory.Alc.inducedSimpleLowestAlcove <;> assumption)
end
