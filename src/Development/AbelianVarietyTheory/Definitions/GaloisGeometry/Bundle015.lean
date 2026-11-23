module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle006
public import Formalism.LocalToGlobal.HermitianForms.Bundle005
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle014
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle099
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle120
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementE
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle008
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AboveL

section Local

variable {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {A : ValuationSubring Ω}
  {v : HeightOneSpectrum (𝓞 K)} {h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v}

def AbW (x : WD h) : Prop :=
  ∀ g g' : Weil h, x.charPol (g * g' * g⁻¹ * g'⁻¹) = (Polynomial.X - 1) ^ x.lpDim

structure Near (x y : WD h) : Prop where
  mono : x.mono0 ↔ y.mono0
  size : ∀ σ : Weil h, (x.eig σ).map (fun z => ‖z‖) = (y.eig σ).map (fun z => ‖z‖)
  eq : ∀ (χ : Weil h →* ℂˣ) (hχ : GlobalTheory.WeilDeligne.IsSmooth χ), IneTriv (y.lpTwist χ hχ) → x = y
  tame : ∀ (χ : Weil h →* ℂˣ) (hχ : GlobalTheory.WeilDeligne.IsSmooth χ), IsTameWD (y.lpTwist χ hχ) →
    ∀ τ : Ine (F := K) A, x.charPol (ineIncl h τ) = y.charPol (ineIncl h τ)

end Local

def SolvDisj {K Ω : Type} (M : Type) [Field K] [Field M] [Field Ω] [Algebra K Ω] [Algebra M Ω] [Algebra K M] [IsScalarTower K M Ω]
    (N : Subgroup (_root_.Formalism.ConjugateSelfDual.G K Ω)) : Prop :=
  IsGalois K M ∧ IsSolvable (M ≃ₐ[K] M) ∧
    ∀ g : _root_.Formalism.ConjugateSelfDual.G K Ω, ∃ (x : _root_.Formalism.ConjugateSelfDual.G M Ω) (n : _root_.Formalism.ConjugateSelfDual.G K Ω), n ∈ N ∧ g = AlgEquiv.restrictScalarsHom K x * n

section API

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

variable {K M : Type} [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] {a : ℕ}

end API

end GlobalTheory.AboveL

end
end

section

noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain _root_.Formalism.L2.Col Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker

section Aut

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def autU (N : Submodule (𝓞 E) (Sp E n)) : Subgroup (UF E n) where
  carrier := {γ | ∀ x, γ.1 x ∈ N ↔ x ∈ N}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb x => (ha (b.1 x)).trans (hb x)
  inv_mem' := fun {a} ha x => by
    have h := ha (a⁻¹.1 x)
    rw [show a.1 (a⁻¹.1 x) = x from LinearEquiv.apply_symm_apply a.1 x] at h
    exact h.symm

theorem mem_autU {N : Submodule (𝓞 E) (Sp E n)} {γ : UF E n} : γ ∈ autU N ↔ gmap γ.1 N = N := by
  constructor
  · intro h
    ext x
    rw [mem_gmap, ← h (γ.1.symm x), LinearEquiv.apply_symm_apply]
  · intro h x
    conv_lhs => rw [← h, mem_gmap, LinearEquiv.symm_apply_apply]

end Aut

section Stab

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem card_dvd_card_autU (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (p : DecoF X.E n ST SG Q)
    (H : Subgroup (FrmG Λ Θ)) (hH : ∀ g ∈ H, g • p = p) : Nat.card H ∣ Nat.card (autU p.deco.1.N) := by
  let f : H →* autU p.deco.1.N :=
    { toFun := fun g => ⟨g.1.1, mem_autU.2 (congrArg (fun q : DecoF X.E n ST SG Q => q.deco.1.N) (hH g.1 g.2))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine Subgroup.card_dvd_of_injective f fun a b hab => ?_
  have h1 : a.1.1 = b.1.1 := congrArg Subtype.val hab
  have ha : FrmG.incl Λ Θ a.1 • p = p := hH a.1 a.2
  have hb : FrmG.incl Λ Θ b.1 • p = p := hH b.1 b.2
  have h2 := DecoSet.stab_fst_injective p.deco (a := ((FrmG.incl Λ Θ a.1).1, (FrmG.incl Λ Θ a.1).2.1))
    (b := ((FrmG.incl Λ Θ b.1).1, (FrmG.incl Λ Θ b.1).2.1)) (congrArg DecoF.deco ha) (congrArg DecoF.deco hb) h1
  exact Subtype.ext (FramedForms.incl_injective Λ Θ (FramedForms.stab_inj p ha hb h1 (Prod.mk.inj h2).2))

end Stab

section Fam

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
  (Λ : LevFam X.E X.K (R.N R.m) Pr.vGs) (Θ : LevQFam X.E X.K (R.N R.m) (QE sel (mu : Chr X.F X.E X.K)))

@[reducible] def frmMem : MemOn (chF W sel mu L u R.m) where
  G := FrmG Λ Θ
  D := ChPt (R := R) sel mu u R.m
  actD := frmAct Λ Θ
  ρ := frmRho (colValF W sel mu u R.m) Λ Θ
  Nab := (colValF W sel mu u R.m).Nab
  Del := (colValF W sel mu u R.m).Del

@[reducible] def cplMem : MemOn (chF W sel mu L u (m2 + 1)) :=
  MemOn.pairs (chF W sel mu L u (m2 + 1)) b (ybCpl W sel mu cst L u m2 b hY)

@[reducible] def levFam : ℕ → GFam X.K :=
  spFam (chF W sel mu L u) m2 R.m (cplMem W sel mu cst L u m2 b hY) (frmMem W sel mu L u Λ Θ)

variable {W sel mu cst L u m2 b hY Λ Θ}

def levPt : ∀ (i : ℕ) (β : (levFam W sel mu cst L u m2 b hY Λ Θ i).β),
    (levFam W sel mu cst L u m2 b hY Λ Θ i).D β → ChPt (R := R) sel mu u i
  | _, .mat _ _ => fun p => p
  | _, .cpl rfl => fun p => p.1.1
  | _, .top rfl => fun p => p

def levG : ∀ (i : ℕ) (_ : (levFam W sel mu cst L u m2 b hY Λ Θ i).β), LevFam X.E X.K (R.N i) Pr.vGs
  | i, .mat al _ => L.levG i al
  | _, .cpl rfl => L.levG (m2 + 1) b
  | _, .top rfl => Λ

def levQ : ∀ (i : ℕ) (_ : (levFam W sel mu cst L u m2 b hY Λ Θ i).β), LevQFam X.E X.K (R.N i) (QE sel (mu : Chr X.F X.E X.K))
  | i, .mat al _ => L.levQ i al
  | _, .cpl rfl => L.levQ (m2 + 1) b
  | _, .top rfl => Θ

def levGrp : ∀ (i : ℕ) (β : (levFam W sel mu cst L u m2 b hY Λ Θ i).β),
    (levFam W sel mu cst L u m2 b hY Λ Θ i).G β ≃* FrmG (levG i β) (levQ i β)
  | _, .mat _ _ => MulEquiv.refl _
  | _, .cpl rfl => MulEquiv.refl _
  | _, .top rfl => MulEquiv.refl _

theorem levPt_smul (i : ℕ) (β : (levFam W sel mu cst L u m2 b hY Λ Θ i).β) (g : (levFam W sel mu cst L u m2 b hY Λ Θ i).G β)
    (d : (levFam W sel mu cst L u m2 b hY Λ Θ i).D β) : levPt i β (g • d) = levGrp i β g • levPt i β d := by
  rcases β with _ | rfl | rfl <;> rfl

theorem card_stab_dvd_autU (i : ℕ) (β : (levFam W sel mu cst L u m2 b hY Λ Θ i).β) (d : (levFam W sel mu cst L u m2 b hY Λ Θ i).D β) :
    Nat.card (MulAction.stabilizer ((levFam W sel mu cst L u m2 b hY Λ Θ i).G β) d) ∣ Nat.card (autU (levPt i β d).deco.1.N) := by
  have h := card_dvd_card_autU (levG i β) (levQ i β) (levPt i β d)
    ((MulAction.stabilizer ((levFam W sel mu cst L u m2 b hY Λ Θ i).G β) d).map (levGrp i β).toMonoidHom) (by
      rintro _ ⟨g, hg, rfl⟩
      exact (levPt_smul i β g d).symm.trans (congrArg (levPt i β) hg))
  rwa [Subgroup.card_map_of_injective (levGrp i β).injective] at h

theorem levFam_ok (hF : ∀ j, (chF W sel mu L u j).Ok) (hT : (frmGSD (colValF W sel mu u R.m) Λ Θ).Ok) (i : ℕ) :
    (levFam W sel mu cst L u m2 b hY Λ Θ i).Ok :=
  spFam_ok (fun j _ => hF j) (cplGSD_ok _ (hF (m2 + 1) b)) hT i

end Fam

end GlobalTheory.GO
end
end

section

noncomputable section

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms _root_.Formalism.L2.Col Formalism.L2.DIV NumberField IsDedekindDomain

abbrev StabDat {D : D7} {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) : Type :=
  ∀ i, C.cls i → Set (Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E × ℂ)

section Gen

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}

def LawAt (O : GL3Theta.LiftObj D C) (i : ℕ) (g : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E × ℂ) (f : C.Y i → ℂ) : Prop :=
  ∀ y y' : C.Y i, (∀ τ, O.frm i y τ = g.1.map (TaylorLogMetric.embT D τ) * O.frm i y' τ) → f y = g.2 * f y'

def FormsAre (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P) (O : GL3Theta.LiftObj D C)
    (G : StabDat C) : Prop :=
  (∀ i, i ≤ D.R.m → ∀ φ ∈ M.Fi i, ∀ c, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) (φ c)) ∧
  ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ φ : C.cls i → C.Y i → ℂ,
    φ ∈ M.Fi i ↔ ∀ c, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) (φ c) ∧ ∀ g ∈ G i c, LawAt O i g (φ c)

def TermLaw (O : GL3Theta.LiftObj D C) (i : ℕ) (c : C.cls i) (c' : C.cls (i + 1))
    (g : Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.host.E × ℂ) : Prop :=
  g.1.det ≠ 0 ∧ ∃ k : ℂ,
    (∀ z : TaylorLogMetric.VC D (D.R.N i) (D.R.N (i + 1)),
      O.Th i c c' (fun τ => (g.1.map (TaylorLogMetric.embT D τ) * Matrix.of (z τ) : Matrix _ _ ℂ)) = k * O.Th i c c' z) ∧
    g.2 = k * ∏ τ, TaylorLogMetric.embT D τ g.1.det ^ (-C.sDiv i τ)

end Gen

def matE {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) : Matrix (Fin n) (Fin n) D.host.E :=
  (LinearMap.toMatrix' γ.toLinearMap).map s.iE

end GlobalTheory.KerJ
end
end

section

noncomputable section

open scoped BigOperators
open Formalism.L2.Th1.H (cmL CmOK matH IsSelfDual Th alphaQ)
open Formalism.L2.Th1.GD (LocNorm)
open Formalism.L2.Th1.E (IntCurve Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.ThLoc

def LatAt (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0) {n : Type} [Fintype n]
    [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime]
    (ι : ℂ ≃+* ℂ_[p]) : Prop :=
  CmOK a₀ b₀ c₀ dK ∧ IsSelfDual (matH h) Λ ∧ (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) ∧
    θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ ∧ LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι

def ThetaZJetsThree : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), d % 8 = 7 → d % 3 = 2 → Formalism.L2.Th1.CM.HasCMBy d L →
  ∀ (ι : ℂ ≃+* ℂ_[3]) (W : WeierstrassCurve ℂ_[3]), Unif 3 L ι W → IntCurve W →
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → Formalism.L2.Th1.CM.omegaK d * (ω₀ / 2) ∉ L.lattice →
    (starRingEnd ℂ) (Formalism.L2.Th1.CM.omegaK d) * (ω₀ / 2) ∉ L.lattice →
  ∀ (n : Type) [Fintype n] (κ : Type) [Fintype κ] (r : κ → ℂ_[3]) (s : κ → n → ℂ) (N : ℕ),
    (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ 3 ∣ N → (∀ k i, (N : ℂ) * s k i ∈ L.lattice) →
    JetsIntegral (Formalism.L2.Th1.Top.thetaZ 3 L ι ω₀ r s)

structure Inputs : Prop where

  jInt : Formalism.L2.Th1.CM.JInvariantIntegrality

  modelTwo : Formalism.L2.Th1.Top.GoodModelTwo

  jetsOdd : Formalism.L2.Th1.GD.IntOpLoc

  jetsTwo : Formalism.L2.Th1.GD.IntOpTwoLoc

  jetsThree : ThetaZJetsThree

  shape : Formalism.L2.Th1.GD.EmbSep → Formalism.L2.Th1.GD.ShapeEigenLoc

  algT : Formalism.L2.KerInert.AlgTAll

  lamExt : Formalism.L2.KerInert.LamExt

namespace LatAt

variable {a₀ : ℕ} {b₀ c₀ : ℤ} {dK : ℕ} {ha : 0 < a₀} {hdK : 0 < dK} {lam : ℂ} {hlam : lam ≠ 0} {n : Type} [Fintype n]
  [DecidableEq n] {h : Matrix n n ℂ} {Λ : AddSubgroup (n → ℂ)} {θ : (n → ℂ) → ℂ} {p : ℕ} [Fact p.Prime] {ι : ℂ ≃+* ℂ_[p]}

theorem selfDual (H : LatAt a₀ b₀ c₀ dK ha hdK lam hlam h Λ θ p ι) : IsSelfDual (matH h) Λ := H.2.1

theorem stable (H : LatAt a₀ b₀ c₀ dK ha hdK lam hlam h Λ θ p ι) : ∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ := H.2.2.1

theorem mem_th (H : LatAt a₀ b₀ c₀ dK ha hdK lam hlam h Λ θ p ι) :
    θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ := H.2.2.2.1

theorem locNorm (H : LatAt a₀ b₀ c₀ dK ha hdK lam hlam h Λ θ p ι) : LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι := H.2.2.2.2

end LatAt

end GlobalTheory.ThLoc
end
end
