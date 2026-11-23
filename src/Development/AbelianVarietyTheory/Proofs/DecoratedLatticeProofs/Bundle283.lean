module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle117
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle146
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle817
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle326
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValDetSubOneLt
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepScalarsOfRealisation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle262
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle279
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle263
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle203
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle207
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle235
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle179
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle267
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle268
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.AdForm.TwDat



theorem chr_root_mul_base {B : Base} {X : PreX B.toPre} {I : TC B X} (hI : I.Ok) {l : I.Laws} {Z : TC.Later B (I.cols l)}
    {u : B.Word} {a : I.ι} {Ch : ℕ → Type} {A : TwDat I l Z u a Ch} (hA : A.Is) (j : Fin B.R.m) (k : ℕ) (hk : k ≤ B.R.m)
    (β : Ch k) (c : {c // A.chOf k c = β}) (x : (AE (I.rec7 l Z))ˣ) (hx : IsDetRoot _ (A.h k β c) x) :
    (A.chr ((j : ℕ) + 1) x : ℂ) * (A.chr ((j : ℕ) + 1) (A.xr k β) : ℂ) =
      ((tildeQ B.host I.SQ (I.C.mu0 j * I.xi a) (detPt B.host I.SQ ((I.stp u a k).rep c.1).1.1) : ℂˣ) : ℂ) := by
  obtain ⟨c, rfl⟩ := c
  have hlev := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hpt := (hA.reads k hk).pt c
  obtain ⟨a', ha'⟩ := GlobalTheory.Mem.DetLift.exists_isDetLift B.R B.host (B.R.N k) _ hpt.uni
  obtain ⟨hkA, hkAm, hxr⟩ := hA.kA k hk (A.chOf k c)
  obtain ⟨hh, hhm⟩ := hA.h k hk (A.chOf k c) ⟨c, rfl⟩
  have hg : A.h k (A.chOf k c) ⟨c, rfl⟩ * A.kA k (A.chOf k c) ∈ GfC _ := mul_mem hh hkA
  have hfin : finM _ (rankN (I.rec7 l Z) k hk) (A.h k (A.chOf k c) ⟨c, rfl⟩ * A.kA k (A.chOf k c)) =
      ((((show TC.GA B (B.R.N k) from ((A.K k hk (A.chOf k c)).y ⟨c, rfl⟩).1) * A.kb k (A.chOf k c) : TC.GA B (B.R.N k))) :
        Matrix (Fin (B.R.N k)) (Fin (B.R.N k)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) := by
    rw [GlobalTheory.RepLattice.finM_mul', hhm, hkAm, Units.val_mul]
    rfl
  have hroot := GlobalTheory.TwistFinPart.isDetRoot_mul' _ _ _ _ _ hx hxr
  have htw := (GlobalTheory.Mem.ReadTwist.isTwist_of_reads B.R B.host _ B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1
  have key := GlobalTheory.DetRootRead.chr_at_detRoot (I.rec7 l Z) (A.chr ((j : ℕ) + 1)) (I.C.mu0 j * I.xi a) (hA.chr j)
    (Formalism.L2.Host.HChar.TrivOn.mul (I.C.isMu0 j).triv htw.2.1) _ _ _ _ hg hfin _ hroot a' ha'
  have hm := reference_characters_factor_tame I.SQ I.C j
  have hxi : KDq B.host I.SQ ≤ ((I.xi a).1.comp (Chr.finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans (hlev.2.2 a).1
  have hfac : KDq B.host I.SQ ≤ ((I.C.mu0 j * I.xi a).1.comp (Chr.finPartI B.host.E)).ker := fun b hb => by
    have e : (I.C.mu0 j).1 (Chr.finPartI B.host.E b) = 1 := hm hb
    have e' : (I.xi a).1 (Chr.finPartI B.host.E b) = 1 := hxi hb
    show (I.C.mu0 j).1 (Chr.finPartI B.host.E b) * (I.xi a).1 (Chr.finPartI B.host.E b) = 1
    rw [e, e', one_mul]
  rw [← GlobalTheory.Mem.Col2.DetSpec.mk_eq_detPt B.R B.host _ _ _ _ _ _ _ a' hlev.1 hpt ha', tildeQ_mk _ _ hfac, ← Circle.coe_mul, ← map_mul]
  exact key

theorem rho_eq {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i + 1 ≤ B.R.m)
    (c : (I.stp u a i).Cl) : (I.chIn u a).rho i c =
      ((tildeQ B.host I.SQ (I.C.mu0 ⟨i, hi⟩ * I.xi a) (detPt B.host I.SQ ((I.stp u a i).rep c).1.1) : ℂˣ) : ℂ)⁻¹ *
        chiId I.C.chiPsi (Th.detId B.host (Th.stdL B.host (B.R.N i)) ((I.stp u a i).rep c).1.1.deco.1.N) ^
          (-((B.R.N (i + 1) / 2 : ℕ) : ℤ)) := by
  have hlev := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hxi : KDq B.host I.SQ ≤ ((I.xi a).1.comp (Chr.finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans (hlev.2.2 a).1
  show ((rhoAt I.SQ I.C (I.xi a) i ((I.stp u a i).rep c).1.1 : ℂˣ) : ℂ) = _
  rw [rhoAt, muTilQ_succ B.host I.SQ I.C.mu0 ⟨i, hi⟩, xiDet, tildeQ_mul B.host I.SQ (reference_characters_factor_tame I.SQ I.C ⟨i, hi⟩) hxi,
    MonoidHom.mul_apply]
  rw [← GlobalTheory.Mem.ChiDet.tildeQ_detPt_eq_chiId B.R B.host _ I.C _ _ _ _ I.SQ _ hlev.1]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, mul_inv]

theorem rho'_eq {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i + 1 ≤ B.R.m)
    (c' : (I.stp u a (i + 1)).Cl) : (I.chIn u a).rho' i c' =
      ((tildeQ B.host I.SQ (I.C.mu0 ⟨i, hi⟩ * I.xi a) (detPt B.host I.SQ ((I.stp u a (i + 1)).rep c').1.1) : ℂˣ) : ℂ) *
        chiId I.C.chiPsi (Th.detId B.host (Th.stdL B.host (B.R.N (i + 1))) ((I.stp u a (i + 1)).rep c').1.1.deco.1.N) ^
          ((B.R.N i / 2 : ℕ) : ℤ) := by
  have hlev := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hxi : KDq B.host I.SQ ≤ ((I.xi a).1.comp (Chr.finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans (hlev.2.2 a).1
  show ((rhoAt' I.SQ I.C (I.xi a) i ((I.stp u a (i + 1)).rep c').1.1 : ℂˣ) : ℂ) = _
  rw [rhoAt', muTilQ_succ B.host I.SQ I.C.mu0 ⟨i, hi⟩, xiDet, tildeQ_mul B.host I.SQ (reference_characters_factor_tame I.SQ I.C ⟨i, hi⟩) hxi,
    MonoidHom.mul_apply]
  rw [← GlobalTheory.Mem.ChiDet.tildeQ_detPt_eq_chiId B.R B.host _ I.C _ _ _ _ I.SQ _ hlev.1]
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]

theorem moves_alg (X Y r₀ r₁ a b : ℂ) (p q : ℤ) (hX : X ≠ 0) (hY : Y ≠ 0) (h₀ : r₀ ≠ 0) (h₁ : r₁ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    X⁻¹ * Y = r₀ * r₁⁻¹ * ((X * r₀)⁻¹ * a ^ (-p) * (Y * r₁ * b ^ q)) * (a ^ p * b ^ (-q)) := by
  have h1 : a ^ p ≠ 0 := zpow_ne_zero p ha
  have h2 : b ^ q ≠ 0 := zpow_ne_zero q hb
  rw [_root_.zpow_neg, _root_.zpow_neg]
  field_simp

theorem chr_moves_eq_rho_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (c : {c // A.chOf i c = α}) (c' : {c // A.chOf (i + 1) c = γ}) x y, IsDetRoot _ (A.h i α c) x → IsDetRoot _ (A.h (i + 1) γ c') y → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) = (A.chr (i + 1) (A.xr i α) : ℂ) * (A.chr (i + 1) (A.xr (i + 1) γ) : ℂ)⁻¹ * ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) * I.A.chiF (B.R.N i) (B.R.N (i + 1)) ((I.stp u a i).rep c.1).1.1.deco.1.N ((I.stp u a (i + 1)).rep c'.1).1.1.deco.1.N := by
  intro B X I hI _ l Z u a Ch A hA i hi α γ c c' x y hx hy
  have h0 := chr_root_mul_base hI hA ⟨i, hi⟩ i (Nat.le_of_succ_le hi) α c x hx
  have h1 := chr_root_mul_base hI hA ⟨i, hi⟩ (i + 1) hi γ c' y hy
  rw [rho_eq I hI u a i hi, rho'_eq I hI u a i hi]
  simp only [ColIn.A, AmbIn.amb, Th.chiFac, ColIn.chi]
  rw [← h0, ← h1]
  exact moves_alg _ _ _ _ _ _ _ _ (Circle.coe_ne_zero _) (Circle.coe_ne_zero _) (Circle.coe_ne_zero _)
    (Circle.coe_ne_zero _) (chiId_ne_zero _ _) (chiId_ne_zero _ _)

end GlobalTheory.AdForm.TwDat
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

theorem _root_.GlobalTheory.T.chainStep_scalars_of_realisation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → SoftQ D → QOfVal D → LPos D → LFull D → StepLam D → ∀ h : RangeX R, RChain R h → NormX R h → RUnif R h → RowPar R → IPDict R → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R := by
  first | exact @GlobalTheory.ChainTw.scalars_of_realisation | exact GlobalTheory.ChainTw.scalars_of_realisation | (intros; apply GlobalTheory.ChainTw.scalars_of_realisation <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.Conj

theorem baseChangeTensorConjugation_involutive_of_involution {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (e : R ⊗[F] E) : sigR R σ (sigR R σ e) = e := by
  induction e using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x => simp [sigR, hσ]

theorem infinitePlaceComponent_tensorConjugation {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    compInf F E w (sigR (AF F) σ z) = sigR w.Completion σ (compInf F E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x => simp [compInf, sigR]

theorem mul_eq_conj_mul_of_invertible_cancel {R : Type*} [Ring R] {P Pi F X K : R} (h1 : P * Pi = 1)
    (h : Pi * F * X = (Pi * K * P) * (Pi * F)) : F * X = K * F := by
  have := congrArg (P * ·) h
  simp only [← mul_assoc, h1, one_mul] at this
  rw [this, mul_assoc K P Pi, h1, mul_one]

theorem eq_inv_conj_of_intertwine {R : Type*} [Ring R] {Fi F X K : R} (h1 : Fi * F = 1) (h : F * X = K * F) :
    X = Fi * K * F := by
  rw [mul_assoc, ← h, ← mul_assoc, h1, one_mul]

variable {D : D7}

theorem matHom_chart_conj (A : HSp D) (μ : D.host.E) (κ : GA D (dblSp A) ≃* G D A.rank) (hκ : IsChart A μ κ)
    (Fr : GL (Fin (A.rank + A.rank)) (AE D)) (p : GA D (dblSp A))
    (hp : mt (dblSp A) p * (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) = Fr.1) (k : GA D (dblSp A)) :
    GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D A.rank) (κ (p⁻¹ * k * p)) =
      Fr⁻¹ * GlobalTheory.AdelicU.matHom (n := A.rank + A.rank) _ D.sp.cm.sig (dblSp A).gram k * Fr := by
  set P := GlobalTheory.AdelicU.matHom (n := A.rank + A.rank) _ D.sp.cm.sig (dblSp A).gram p
  set Kk := GlobalTheory.AdelicU.matHom (n := A.rank + A.rank) _ D.sp.cm.sig (dblSp A).gram k
  have hmt : ∀ g, mt (dblSp A) g = (GlobalTheory.AdelicU.matHom (n := A.rank + A.rank) _ D.sp.cm.sig (dblSp A).gram g).1 := fun _ => rfl
  have hT : (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) = (P⁻¹).1 * Fr.1 := by
    rw [← hp, hmt, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have h := hκ (p⁻¹ * k * p)
  have hm : GlobalTheory.AdelicU.matHom (n := A.rank + A.rank) _ D.sp.cm.sig (dblSp A).gram (p⁻¹ * k * p) = P⁻¹ * Kk * P := by
    rw [map_mul, map_mul, map_inv]
  rw [hmt, hm, hT] at h
  change (P⁻¹).1 * Fr.1 * mat (κ (p⁻¹ * k * p)) = (P⁻¹ * Kk * P).1 * ((P⁻¹).1 * Fr.1) at h
  apply Units.ext
  have h2 : Fr.1 * mat (κ (p⁻¹ * k * p)) = Kk.1 * Fr.1 := by
    rw [Units.val_mul, Units.val_mul] at h
    exact mul_eq_conj_mul_of_invertible_cancel (P := P.1) (Units.mul_inv P) h
  change mat (κ (p⁻¹ * k * p)) = _
  rw [Units.val_mul, Units.val_mul]
  exact eq_inv_conj_of_intertwine (Units.inv_mul Fr) h2

theorem mem_KAd_iff_of_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (Q J : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a b : GL (Fin n) (AF F ⊗[F] E)) (hb : _root_.GlobalTheory.AdelicU.IsLatticeFrame L b)
    (hab : ∀ w, Formalism.UG.bc (compInf F E w) b = Formalism.UG.bc (compInf F E w) a)
    (M M' : GL (Fin (n + n)) (AF F ⊗[F] E)) (u r : (AF F ⊗[F] E)ˣ)
    (hM' : ∀ v i j, compFin F E v (M'.1 i j) ∈ intLoc F E v ∧ compFin F E v ((M'⁻¹).1 i j) ∈ intLoc F E v)
    (hMu : M.1 = (u : AF F ⊗[F] E) • M'.1)
    (hMM : ∀ w, (Formalism.UG.cT (sigR (AF F) σ) M.1 * M.1).map (compInf F E w) = compInf F E w r • 1)
    (k : GAd σ Q) (g : GAd σ J)
    (hg : GlobalTheory.AdelicU.matHom _ σ J g = (blkGL finSumFinEquiv (b, b) * M)⁻¹ * GlobalTheory.AdelicU.matHom _ σ Q k *
      (blkGL finSumFinEquiv (b, b) * M)) :
    k ∈ KAd σ Q L a ↔ g ∈ levelAll σ J (stdLattice E (n + n)) 1 := by
  rw [mem_KAd, mem_levelAll]
  refine and_congr (forall_congr' fun v => ?_) (forall_congr' fun w => ?_)
  · rw [GlobalTheory.Doubling.KFin, stabLoc, stabLoc, Subgroup.mem_comap, Subgroup.mem_comap, matHom_proj, matHom_proj, hg,
      map_mul (Formalism.UG.bc (compFin F E v)), map_mul (Formalism.UG.bc (compFin F E v)) _ (GlobalTheory.AdelicU.matHom _ σ Q k), map_inv]
    exact GlobalTheory.T.mem_latticeStabilizer_iff_scaledFrameConj F E (n + n) _ _ M M' u (isLatticeFrame_dbl hb) hM' hMu v _
  · have hc : Formalism.UG.cT (sigR w.Completion σ) (Formalism.UG.bc (compInf F E w) M).1 * (Formalism.UG.bc (compInf F E w) M).1 =
        ((Units.map (compInf F E w : AF F ⊗[F] E →* w.Completion ⊗[F] E) r : (w.Completion ⊗[F] E)ˣ) :
          w.Completion ⊗[F] E) • 1 := by
      have h := hMM w
      rw [Matrix.map_mul] at h
      refine Eq.trans ?_ h
      congr 1
      ext i j
      exact (infinitePlaceComponent_tensorConjugation σ w (M.1 j i)).symm
    rw [KArch, mem_stabArch, mem_stabArch, matHom_projArch, matHom_projArch, hg,
      GlobalTheory.T.mem_unitaryStandard_iff_conj_similitude _ _ (baseChangeTensorConjugation_involutive_of_involution _ σ hσ) _ _ _ _ hc]
    simp only [map_mul, map_inv, map_one, bc_blkGL, hab w, inv_one, one_mul, mul_one, mul_inv_rev, mul_assoc]

theorem isConj_of_frame : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (a b : GL (Fin A.rank) (AE D)), _root_.GlobalTheory.AdelicU.IsLatticeFrame (frameLat A) b → (∀ w, Formalism.UG.bc (compInf D.host.F D.host.E w) b = Formalism.UG.bc (compInf D.host.F D.host.E w) a) → ∀ (M M' : GL (Fin (A.rank + A.rank)) (AE D)) (u : (AE D)ˣ), IntGL M' → M.1 = (u : AE D) • M'.1 → (∀ w, (adj M.1 * M.1).map (compInf D.host.F D.host.E w) = compInf D.host.F D.host.E w (2 * u * cA D u) • 1) → ∀ p : siegel A, mt (dblSp A) p * (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) = (blkGL finSumFinEquiv (b, b) * M).1 → IsConj A a κ p := by
  intro D A μ _ κ hκ a b hb hab M M' u hM' hMu hMM p hp k
  have h2 : IsUnit (2 : AE D) := by
    have := (IsUnit.mk0 (2 : D.host.E) two_ne_zero).map (incA D)
    rwa [map_ofNat] at this
  have hr : IsUnit (2 * (u : AE D) * cA D u) := (h2.mul u.isUnit).mul (u.isUnit.map (cA D))
  have hg := matHom_chart_conj A μ κ hκ (blkGL finSumFinEquiv (b, b) * M) p hp k
  have hMM' : ∀ w, (Formalism.UG.cT (cA D) M.1 * M.1).map (compInf D.host.F D.host.E w) =
      compInf D.host.F D.host.E w hr.unit • 1 := hMM
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have key := mem_KAd_iff_of_conj (n := A.rank) D.sp.cm.sig hσ (dblSp A).gram (Jst D A.rank) (frameLat A) a b hb hab
    M M' u hr.unit (fun v i j => ⟨hM'.1 i j v, hM'.2 i j v⟩) hMu hMM' k (κ ((p : GA D (dblSp A))⁻¹ * k * p)) hg
  have e : K D A.rank = levelAll D.sp.cm.sig (Jst D A.rank) (stdLattice D.host.E (A.rank + A.rank)) 1 := rfl
  rw [e]
  exact key

end GlobalTheory.StdUnn.Conj

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainNS
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainNS

theorem chainNS_holds : ∀ D : D7, ChainNS D := by
  intro D c hc S' hS' B hB hBi k hk
  obtain ⟨p, hp, -, hpS, v, hv⟩ :=
    GlobalTheory.SplitChoice.exists_split_prime D (S' : Set (HeightOneSpectrum (𝓞 D.host.F))) 1 (Finset.finite_toSet _) one_ne_zero
  have hvS : v ∉ S' := fun h => hpS v (Finset.mem_coe.2 h) hv
  refine ⟨v, hvS, GlobalTheory.SplitPlace.isSplit_of_splitsCompletely D p hp v hv, ?_⟩
  intro w hw β hβ k' hk'
  have hrt5 : D.R.r + 5 ≤ D.R.t := D.R.rank_add_five_le
  have hrt : D.R.r + 2 ≤ D.R.t := by omega
  have hwS : w ∉ GlobalTheory.LFun.above D.host.E (S' : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
    simp [GlobalTheory.LFun.above, hw, hvS]
  have hpw : ((p : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    have h := hv
    rw [← hw, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at h
    exact h
  have hwc : w.under (𝓞 D.host.F) ∉ c.S := fun h => hvS (hw ▸ hS' h)
  set x := GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)) w with hx
  have hmem : x⁻¹ * β ∈ GlobalTheory.LFun.twist (chainPar c B k) (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)))⁻¹ w := by
    simp only [GlobalTheory.LFun.twist, Pi.inv_apply]
    exact Multiset.mem_map_of_mem _ hβ
  rw [chainPar_twist_chT] at hmem
  have key : ((x⁻¹ * β : ℂˣ) : ℂ) ≠ GlobalTheory.LFun.npow w ((k' : ℂ) / 2) := by
    have hN := GlobalTheory.T.small_entries_and_strings_avoid_excluded_norm_powers D.host.E w D.R.r D.R.t hrt k' hk'
    simp only [Pi.add_apply, Finset.sum_apply, Multiset.mem_add, Multiset.mem_sum] at hmem
    rcases hmem with h | ⟨i, hi, h⟩
    · simp only [GlobalTheory.LFun.twist, Pi.inv_apply] at h
      obtain ⟨b, hb, hb'⟩ := Multiset.mem_map.1 h
      rw [← hb']
      have hb1 := (hB w hwS).2 b hb
      have hb2 := (hBi w hwS).2 b⁻¹ (Multiset.mem_map_of_mem _ hb)
      have hu : ‖((GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)) w : ℂˣ) : ℂ)‖ = 1 := GlobalTheory.LFun.norm_val _ _
      refine hN.1 _ (Units.ne_zero _) ?_ ?_
      · rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one, one_mul]
        exact hb1
      · rw [Units.val_mul, mul_inv, norm_mul, Units.val_inv_eq_inv_val, inv_inv, hu, one_mul]
        rw [Units.val_inv_eq_inv_val] at hb2
        exact hb2
    · have hi' := Finset.mem_Icc.1 hi
      exact hN.2 _ (GlobalTheory.LFun.norm_val _ _)
        (GlobalTheory.T.heckeCharQuotient_ne_one_completelySplitPrime D c hc i (k + 1) hi'.1 (by omega) (by omega) p hp w hpw hwc) _ h
  intro he
  apply key
  rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_comm]
  exact he

end GlobalTheory.ChainNS
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.standardUnitaryChart_blockDiagonal_eq_levi : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (g : GA D (dblSp A)) (a : GL (Fin A.rank) (AE D)), mat (κ g) = blk4 a.1 0 0 (adj (a⁻¹).1) → g = (dblDec A).levi a := by
  first | exact @GlobalTheory.StdUnn.chart_levi | exact GlobalTheory.StdUnn.chart_levi | (intros; apply GlobalTheory.StdUnn.chart_levi <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.standardUnitaryChart_unipotent_eq_wittUnipotent : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (g : GA D (dblSp A)) (b : Mx D A.rank A.rank), mat (κ g) = blk4 1 b 0 1 → ∃ c : skewA D A.rank, c.1 = incA D μ⁻¹ • b ∧ g = (dblDec A).nC c := by
  first | exact @GlobalTheory.ChartUnip.chart_unip | exact GlobalTheory.ChartUnip.chart_unip | (intros; apply GlobalTheory.ChartUnip.chart_unip <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.ChartExist

open Formalism.UG

variable {R : Type} [CommRing R]

theorem cT_mul_gen (σ : R →+* R) {m p q : Type} [Fintype p] (M : Matrix m p R) (N : Matrix p q R) :
    cT σ (M * N) = cT σ N * cT σ M := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one_gen (σ : R →+* R) {n : Type} [Fintype n] [DecidableEq n] : cT σ (1 : Matrix n n R) = 1 := by
  simp [cT]

variable {n : Type} [Fintype n] [DecidableEq n]

theorem conj_mem (σ : R →+* R) (Q J : Matrix n n R) (T : GL n R) (c : Rˣ)
    (hT : cT σ (T : Matrix n n R) * Q * T = (c : R) • J) (g : GL n R) (hg : g ∈ UJ σ Q) :
    T⁻¹ * g * T ∈ UJ σ J := by
  have hg' : cT σ (g : Matrix n n R) * Q * g = Q := hg
  show cT σ (((T⁻¹ * g * T : GL n R)) : Matrix n n R) * J * ((T⁻¹ * g * T : GL n R) : Matrix n n R) = J
  have h1 : ((T⁻¹ : GL n R) : Matrix n n R) * T = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : (T : Matrix n n R) * ((T⁻¹ : GL n R) : Matrix n n R) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h3 : cT σ ((T⁻¹ : GL n R) : Matrix n n R) * cT σ (T : Matrix n n R) = 1 := by
    rw [← cT_mul_gen, h2, cT_one_gen]
  have hJ : J = ((c⁻¹ : Rˣ) : R) • (cT σ (T : Matrix n n R) * Q * T) := by
    rw [hT, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [hJ]
  simp only [Units.val_mul, cT_mul_gen, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc _ = cT σ (T : Matrix n n R) * cT σ (g : Matrix n n R) *
        (cT σ ((T⁻¹ : GL n R) : Matrix n n R) * cT σ (T : Matrix n n R)) * Q *
        ((T : Matrix n n R) * ((T⁻¹ : GL n R) : Matrix n n R)) * g * T := by
          simp only [Matrix.mul_assoc]
    _ = cT σ (T : Matrix n n R) * (cT σ (g : Matrix n n R) * Q * g) * T := by
          rw [h3, h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = cT σ (T : Matrix n n R) * Q * T := by rw [hg']

theorem conj_back (σ : R →+* R) (Q J : Matrix n n R) (T : GL n R) (c : Rˣ)
    (hT : cT σ (T : Matrix n n R) * Q * T = (c : R) • J) :
    cT σ ((T⁻¹ : GL n R) : Matrix n n R) * J * ((T⁻¹ : GL n R) : Matrix n n R) = ((c⁻¹ : Rˣ) : R) • Q := by
  have h2 : (T : Matrix n n R) * ((T⁻¹ : GL n R) : Matrix n n R) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h3 : cT σ ((T⁻¹ : GL n R) : Matrix n n R) * cT σ (T : Matrix n n R) = 1 := by
    rw [← cT_mul_gen, h2, cT_one_gen]
  have hJ : J = ((c⁻¹ : Rˣ) : R) • (cT σ (T : Matrix n n R) * Q * T) := by
    rw [hT, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [hJ, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc cT σ ((T⁻¹ : GL n R) : Matrix n n R) * (cT σ (T : Matrix n n R) * Q * T) * ((T⁻¹ : GL n R) : Matrix n n R)
      = (cT σ ((T⁻¹ : GL n R) : Matrix n n R) * cT σ (T : Matrix n n R)) * Q *
        ((T : Matrix n n R) * ((T⁻¹ : GL n R) : Matrix n n R)) := by simp only [Matrix.mul_assoc]
    _ = Q := by rw [h3, h2, Matrix.one_mul, Matrix.mul_one]

def conjEquiv (σ : R →+* R) (Q J : Matrix n n R) (T : GL n R) (c : Rˣ)
    (hT : cT σ (T : Matrix n n R) * Q * T = (c : R) • J) : UJ σ Q ≃* UJ σ J where
  toFun g := ⟨T⁻¹ * g.1 * T, conj_mem σ Q J T c hT g.1 g.2⟩
  invFun h := ⟨T * h.1 * T⁻¹, by
    have := conj_mem σ J Q T⁻¹ c⁻¹ (conj_back σ Q J T c hT) h.1 h.2
    rwa [inv_inv] at this⟩
  left_inv g := by ext1; simp [mul_assoc]
  right_inv h := by ext1; simp [mul_assoc]
  map_mul' g h := by ext1; simp [mul_assoc]

end GlobalTheory.StdUnn.ChartExist


open GlobalTheory.StdUnn.ChartExist in
theorem GlobalTheory.StdUnn.ChartExist.gram_adelic (D : D7) (A : HSp D) (μ : D.host.E)
    (hgram : (Tm A μ)ᴴ * (dblSp A).gram * Tm A μ = μ • Jst D A.rank)
    (T : GL (Fin (A.rank + A.rank)) (AE D)) (hTv : T.val = rat (Tm A μ)) (c : (AE D)ˣ) (hc : (c : AE D) = incA D μ) :
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) T.val
      * (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF D.host.F) (dblSp A).gram : Matrix (Fin (A.rank + A.rank)) (Fin (A.rank + A.rank)) (AE D)) * T.val
      = (c : AE D) • Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF D.host.F) (Jst D A.rank) := by
  have e1 : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) T.val = ((Tm A μ)ᴴ).map (incA D) := by
    rw [hTv]; ext i j; rfl
  rw [e1, hTv, hc]
  change ((Tm A μ)ᴴ).map (incA D) * ((dblSp A).gram).map (incA D) * (Tm A μ).map (incA D) = (incA D μ) • (Jst D A.rank).map (incA D)
  rw [← Matrix.map_mul, ← Matrix.map_mul, hgram]
  ext i j
  simp [Matrix.map_apply, map_mul]


open GlobalTheory.StdUnn.ChartExist in
theorem GlobalTheory.StdUnn.chart_exists : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∃ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ := by
  intro D A μ hμ
  obtain ⟨hgram, hdet, -⟩ := GlobalTheory.StdUnn.Tm_gram_inv D A μ hμ
  have hdetR : IsUnit (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)).det := by
    have : (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)).det = incA D (Tm A μ).det := by
      rw [RingHom.map_det]; rfl
    rw [this]; exact hdet.map (incA D)
  let T : GL (Fin (A.rank + A.rank)) (AE D) := Matrix.nonsingInvUnit _ hdetR
  have hTv : T.val = rat (Tm A μ) := rfl
  have hμu : IsUnit (incA D μ) := (Ne.isUnit hμ.1).map (incA D)
  refine ⟨conjEquiv (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) _ _ T hμu.unit
    (gram_adelic D A μ hgram T hTv hμu.unit hμu.unit_spec), ?_⟩
  intro g
  show (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) * (T⁻¹ * g.1 * T).val = g.1.val * rat (Tm A μ)
  rw [← hTv]
  simp only [Units.val_mul, ← Matrix.mul_assoc]
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
end
