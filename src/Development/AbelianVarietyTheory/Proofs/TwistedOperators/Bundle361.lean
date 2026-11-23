module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle332
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle103
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle344
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly

section Darboux

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def darbAlg {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w) : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ) :=
  Submodule.span ℂ {Φ | ∃ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      f ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.Pol M ψ τ ∧ (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) ∧
      (∀ᶠ v in Filter.cofinite, φ v = M.vac v) ∧ Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ}


open Classical in
def liftPure {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    {P : Type} [AddCommGroup P] [Module ℂ P] (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    {N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v) :
    ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] P ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens s :=
  if H : ∃ q : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] P ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens s,
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        q (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v))
  then H.choose else 0

end Darboux

theorem exists_rtensOp {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] (s : ∀ i, N i)
    (a : ∀ i, Module.End ℂ (N i)) :
    ∃ T : Module.End ℂ (GlobalTheory.SmallThetaModules.RTens s), ∀ ξ, Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ →
      T (GlobalTheory.SmallThetaModules.pureT s ξ) = GlobalTheory.SmallThetaModules.pureT s (fun i => a i (ξ i)) :=
  GlobalTheory.SmallThetaModules.exists_lift s (GlobalTheory.SmallThetaModules.pureT s)
    (fun l hl => GlobalTheory.SmallThetaModules.pureT_sep s l hl) s a

variable {D : D7}

def vacIm {a a' : ℕ} (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F a a') :
    ∀ v, Rf.Pi v := fun v => Rf.p v (Γ.M.vac v)

abbrev PiT {a a' : ℕ} (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F a a') (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F a a') : Type :=
  R.Pi ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens (vacIm Γ Rf)


open Classical in
def thetaLift {m k d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) (ψ : AddChar (AF D.host.F) ℂ) (G : Matrix (Fin m) (Fin m) D.host.E)
    (e : Fin k ≃ Fin d) (S : Submodule ℂ ((Fin m × Fin k → AF D.host.F) → ℂ)) {P : Type} [AddCommGroup P] [Module ℂ P]
    (pD : ((Fin m × Fin k → AF D.host.F) → ℂ) →ₗ[ℂ] P) : (Matrix (Fin d) (Fin m) (AE D) → ℂ) →ₗ[ℂ] P :=
  if H : ∃ q : (Matrix (Fin d) (Fin m) (AE D) → ℂ) →ₗ[ℂ] P, ∀ Ψ ∈ S, q (GlobalTheory.TripleRead.thO Mo ψ G e Ψ) = pD Ψ
  then H.choose else 0

def mapA (ψ : AddChar (AF D.host.F) ℂ) {W W₁ X : HSp D} (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F W.rank W₁.rank) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F W.rank W₁.rank) :
    (WO W X → ℂ) →ₗ[ℂ] PiT R Γ Rf :=
  thetaLift Γ.M ψ (sgn true W).gram e (darbAlg Γ.M Bs.ψ Bs.emb) (liftPure Γ.M R.p Rf.p (vacIm Γ Rf))

def mapB (ψ : AddChar (AF D.host.F) ℂ) {W W₁ X : HSp D} (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F W.rank W₁.rank) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F W.rank W₁.rank) :
    (WO W₁ X → ℂ) →ₗ[ℂ] PiT R Γ Rf :=
  thetaLift Γ.M' ψ (sgn false W₁).gram e (darbAlg Γ.M' Bs.ψ Bs.emb) (liftPure Γ.M' R.p' Rf.p' (vacIm Γ Rf))


open Classical in
def opFin {M X : HSp D} (ω : WRep M X) (S : Submodule ℂ (WO M X → ℂ)) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : (WO M X → ℂ) →ₗ[ℂ] P) (h : GA D X) : Module.End ℂ P :=
  if H : ∃ T : Module.End ℂ P, ∀ Φ ∈ S, p (ω (1, h) Φ) = T (p Φ) then H.choose else 1


open Classical in
def opLie (θ : InfFam D) {M X : HSp D} (ω : WRep M X) (S : Submodule ℂ (WO M X → ℂ)) {P : Type} [AddCommGroup P]
    [Module ℂ P] (p : (WO M X → ℂ) →ₗ[ℂ] P) (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) : Module.End ℂ P :=
  if H : ∃ T : Module.End ℂ P, ∀ Φ ∈ S, ∀ Φ' ∈ S, IsDer θ X (fun h => ω (1, h)) τ Y Φ Φ' → p Φ' = T (p Φ)
  then H.choose else 0

end GlobalTheory.TripleAssembly

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.HtInfKapX

open GlobalTheory.AdelicU (htInf htOf normInf opNorm compInf)

theorem opNorm_reindex_le {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (y : Matrix n n ℂ) : opNorm (reindex e e y) ≤ opNorm y := by
  unfold GlobalTheory.AdelicU.opNorm
  refine ContinuousLinearMap.opNNNorm_le_bound _ _ fun x => ?_
  let c : EuclideanSpace ℂ m → EuclideanSpace ℂ n := fun z => WithLp.toLp 2 fun i => z (e i)
  let c' : EuclideanSpace ℂ n → EuclideanSpace ℂ m := fun z => WithLp.toLp 2 fun j => z (e.symm j)
  have hc : ∀ z, ‖c z‖₊ = ‖z‖₊ := fun z => by
    simp only [EuclideanSpace.nnnorm_eq, c]
    congr 1
    exact Equiv.sum_comp e (fun j => ‖z j‖₊ ^ 2)
  have hc' : ∀ z, ‖c' z‖₊ = ‖z‖₊ := fun z => by
    simp only [EuclideanSpace.nnnorm_eq, c']
    congr 1
    exact Equiv.sum_comp e.symm (fun j => ‖z j‖₊ ^ 2)
  have h : Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) (reindex e e y) x =
      c' (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y (c x)) := by
    ext j
    change ∑ k, y (e.symm j) (e.symm k) * x k = ∑ i, y (e.symm j) i * x (e i)
    rw [← Equiv.sum_comp e]
    simp
  rw [h, hc', ← hc x]
  exact ContinuousLinearMap.le_opNNNorm _ _

theorem opNorm_reindex {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (y : Matrix n n ℂ) : opNorm (reindex e e y) = opNorm y := by
  refine le_antisymm (opNorm_reindex_le e y) ?_
  have h : reindex e.symm e.symm (reindex e e y) = y := by ext; simp
  calc opNorm y = opNorm (reindex e.symm e.symm (reindex e e y)) := by rw [h]
    _ ≤ opNorm (reindex e e y) := opNorm_reindex_le e.symm _

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  (w : NumberField.InfinitePlace F)

theorem normInf_reindex {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (y : Matrix n n (w.Completion ⊗[F] E)) : normInf F w (reindex e e y) = normInf F w y := by
  unfold GlobalTheory.AdelicU.normInf
  congr 1
  funext τ
  rw [reindex_apply, ← Matrix.submatrix_map, ← reindex_apply, opNorm_reindex]

theorem htInf_reindex {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (g : (Matrix n n (w.Completion ⊗[F] E))ˣ) :
    htInf F w (Units.map (Matrix.reindexAlgEquiv (w.Completion ⊗[F] E) (w.Completion ⊗[F] E) e).toMonoidHom g) =
      htInf F w g := by
  have key : ∀ y, normInf F w ((Matrix.reindexAlgEquiv (w.Completion ⊗[F] E) (w.Completion ⊗[F] E) e) y) =
      normInf F w y := fun y => by rw [Matrix.reindexAlgEquiv_apply, normInf_reindex]
  show GlobalTheory.AdelicU.htOf (normInf F w) _ = GlobalTheory.AdelicU.htOf (normInf F w) _
  rw [GlobalTheory.AdelicU.htOf, GlobalTheory.AdelicU.htOf, ← map_inv, Units.coe_map, Units.coe_map]
  exact congrArg₂ _ rfl (congrArg₂ _ (key _) (key _))

theorem bc_reindex {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n m : Type} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (e : n ≃ m) (g : (Matrix n n A)ˣ) :
    Formalism.UG.bc φ (Units.map (Matrix.reindexAlgEquiv A A e).toMonoidHom g) =
      Units.map (Matrix.reindexAlgEquiv B B e).toMonoidHom (Formalism.UG.bc φ g) := by
  ext i j
  rfl

theorem htInf_kapX_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • reindex e e X.gramᵀ), ∃ C : NNReal, ∀ h : GA D X, ∏ w, GlobalTheory.AdelicU.htInf D.host.F w (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (kapX X e hJ h).1) ≤ C * ∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ X τ h := by
  intro D θ hθ X d e J hJ
  refine ⟨1, fun h => ?_⟩
  rw [one_mul]
  refine le_of_eq ?_
  have key : ∀ w, GlobalTheory.AdelicU.htInf D.host.F w
      (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (kapX X e hJ h).1) =
      GlobalTheory.AdelicU.htInf D.host.F w (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (Formalism.L2.Theta.matHom X h)) :=
    fun w => by
      show GlobalTheory.AdelicU.htInf D.host.F w (Formalism.UG.bc _
        (Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (Formalism.L2.Theta.matHom X h))) = _
      rw [bc_reindex, htInf_reindex]
  simp only [key]
  exact (Function.Bijective.prod_comp (GlobalTheory.CMTypePlaces.places_bijective D) _).symm.trans
    (Finset.prod_congr rfl fun τ _ => GlobalTheory.Grow.htInf_eq_infHt X hθ τ h)

end GlobalTheory.HtInfKapX
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.InfKill

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def infIncl (F : Type) [Field F] [NumberField F] : Ainf F →ₗ[F] AF F where
  toFun a := ((a, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  map_add' a b := by
    show ((a + b, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = ((a, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) + ((b, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
    simp
  map_smul' c a := by
    show ((c • a, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = c • ((a, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
    simp

theorem smul_eq_zero_of_fst (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : AF F ⊗[F] E) (hx : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x = 0) (u : AF F)
    (hu : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u) : u • x = 0 := by
  let e : AF F := ((1, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (1 - e) = 0 := by
    have : (1 - e).1 = 0 := by
      show ((1 : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) - ((1, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)).1 = 0
      simp
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI, this, map_zero]
  have hu' : u = u * e := by
    have := hu (1 - e) h1
    rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at this
    rw [mul_comm]; exact this
  have key : ∀ y : AF F ⊗[F] E,
      e • y = (infIncl F).rTensor E (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
      congr 1
      show ((1, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) * (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from a) =
        (((show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from a).1, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
      refine Prod.ext ?_ ?_
      · exact one_mul _
      · exact zero_mul _
    | add y z hy hz => rw [smul_add, hy, hz, map_add (f := _), map_add (f := _)]
  rw [hu', mul_smul, key, hx, map_zero, smul_zero]

end GlobalTheory.InfKill

namespace GlobalTheory.InfKill

open GlobalTheory.SquareAgree

theorem smul_mat_kapX_sub_one : (∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ), ∀ g ∈ GfC X, ∀ u : AF D.host.F,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (kapX X e hJ g) - 1) = 0) := by
  intro D X d e J hJ g hg u hu
  rw [mat_kapX]
  have h1 : (infHom X g).val = 1 := by rw [show infHom X g = 1 from hg]; rfl
  have hM : ∀ a b, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((Formalism.L2.Theta.mt X g - 1) a b) = 0 := by
    intro a b
    have e2 := congrFun (congrFun h1 a) b
    rw [Matrix.sub_apply, map_sub]
    refine sub_eq_zero.2 ((congrArg id e2).trans ?_)
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hr : Matrix.reindex e e (Formalism.L2.Theta.mt X g) - 1 = Matrix.reindex e e (Formalism.L2.Theta.mt X g - 1) := by
    ext i j
    simp [Matrix.one_apply, e.symm.injective.eq_iff]
  rw [hr]
  ext i j
  rw [Matrix.smul_apply, Matrix.zero_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact smul_eq_zero_of_fst _ _ _ (hM _ _) u hu

end GlobalTheory.InfKill

end
end

section

noncomputable section

namespace GlobalTheory.HoweGlobal

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}

def algAt (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (T : Finset (Pl F)) :
    Submodule ℂ ((Fin n × Fin d → AF F) → ℂ) :=
  Submodule.span ℂ {Φ | ∃ f φ, f ∈ M.Pol ψ emb ∧ (∀ v, φ v ∈ SB _) ∧ (∀ v ∉ T, φ v = M.vac v) ∧ Φ = pure f φ}

variable (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w)

theorem algAt_mono {T T' : Finset (Pl F)} (h : T ⊆ T') : algAt M ψ emb T ≤ algAt M ψ emb T' := by
  refine Submodule.span_mono ?_
  rintro Φ ⟨f, φ, hf, hφ, hv, rfl⟩
  exact ⟨f, φ, hf, hφ, fun v hv' => hv v fun h' => hv' (h h'), rfl⟩

theorem exists_algAt {Φ : (Fin n × Fin d → AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.SquareAgree.algD M ψ emb)
    (T₀ : Finset (Pl F)) : ∃ T, T₀ ⊆ T ∧ Φ ∈ algAt M ψ emb T := by
  classical
  induction hΦ using Submodule.span_induction generalizing T₀ with
  | mem x hx =>
    obtain ⟨f, φ, hf, hφ, hco, rfl⟩ := hx
    have hfin : {v | ¬ φ v = M.vac v}.Finite := Filter.eventually_cofinite.1 hco
    refine ⟨T₀ ∪ hfin.toFinset, Finset.subset_union_left, Submodule.subset_span ⟨f, φ, hf, hφ, fun v hv => ?_, rfl⟩⟩
    by_contra hne
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hne))
  | zero => exact ⟨T₀, subset_rfl, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨T₁, h₁, hx₁⟩ := hx T₀
    obtain ⟨T₂, h₂, hy₂⟩ := hy T₁
    exact ⟨T₂, h₁.trans h₂, add_mem (algAt_mono M ψ emb h₂ hx₁) hy₂⟩
  | smul c x _ hx =>
    obtain ⟨T₁, h₁, hx₁⟩ := hx T₀
    exact ⟨T₁, h₁, Submodule.smul_mem _ c hx₁⟩

end GlobalTheory.HoweGlobal

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SquareAgree

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

structure IsThetaSubG (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (om : Rep σ X W)
    (N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop where

  le : N ≤ algD M ψ emb

  fin : ∀ (v : Pl (F := F)) (f : SInf F (Fin n × Fin d)) (φ : ∀ w : Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ), f ∈ M.Pol ψ emb →
    (∀ w, φ w ∈ SB _) → (∀ᶠ w in Filter.cofinite, φ w = M.vac w) → φ v ∈ augAt om v → pure f φ ∈ N

  lie : ∀ γ ∈ Lines σ X, ∀ f ∈ M.Pol ψ emb, ∀ f₁ ∈ M.Pol ψ emb,
    ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
    ∀ φ : ∀ w : Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ, (∀ w, φ w ∈ SB _) → (∀ᶠ w in Filter.cofinite, φ w = M.vac w) →
      pure f₁ φ ∈ N

  cpt : ∀ k ∈ KInf σ X emb, ∀ f ∈ M.Pol ψ emb, ∀ f₁ ∈ M.Pol ψ emb, Acts (evI F) (om (k, 1)) f f₁ →
    ∀ φ : ∀ w : Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ, (∀ w, φ w ∈ SB _) → (∀ᶠ w in Filter.cofinite, φ w = M.vac w) →
      pure f₁ φ - pure f φ ∈ N

  stabFin : ∀ (v : Pl (F := F)), ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ N, om (1, h) Φ ∈ N

  stabLie : ∀ γ ∈ Lines σ W, ∀ Φ ∈ N, ∀ Φ₁ ∈ algD M ψ emb,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → Φ₁ ∈ N

  stabCpt : ∀ k ∈ KInf σ W emb, ∀ Φ ∈ N, om (1, k) Φ ∈ N

theorem IsDatum.fun_eq (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {Z : Type}
    (crd : Matrix (Fin n) (Fin d) (AE F E) → Z) (hc : Function.Surjective crd) {Φ : (Fin n × Fin d → AF F) → ℂ} {f f' : Z → ℂ}
    (h : IsDatum M ψ crd Φ f) (h' : IsDatum M ψ crd Φ f') : f = f' := by
  funext z
  obtain ⟨u, rfl⟩ := hc z
  rw [← h.2 u, ← h'.2 u]

end GlobalTheory.SquareAgree

end
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.PolKerLieV

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem exists_decomp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ) (emb : (w : InfinitePlace F) → GlobalTheory.AdelicU.EmbOver E w)
    {Φ : (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.SquareAgree.algD M ψ emb) :
    ∃ (T : Finset (Pl F)) (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d))
      (φ : Fin m → (v : Pl F) → (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
        ∀ v ∉ T, φ i v = M.vac v) ∧
      Φ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) := by
  classical
  unfold GlobalTheory.SquareAgree.algD at hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hφ, hv, rfl⟩ := hx
    have hfin := Filter.eventually_cofinite.1 hv
    refine ⟨hfin.toFinset, 1, fun _ => f, fun _ => φ, fun _ => ⟨hf, hφ, fun v hvT => ?_⟩, by simp⟩
    by_contra h
    exact hvT (hfin.mem_toFinset.2 h)
  | zero =>
    exact ⟨∅, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨T₁, m₁, f₁, φ₁, h₁, rfl⟩ := hx
    obtain ⟨T₂, m₂, f₂, φ₂, h₂, rfl⟩ := hy
    refine ⟨T₁ ∪ T₂, m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, fun i => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Fin.append_left]
        exact ⟨(h₁ i).1, (h₁ i).2.1, fun v hv => (h₁ i).2.2 v (fun h => hv (Finset.mem_union_left _ h))⟩
      · simp only [Fin.append_right]
        exact ⟨(h₂ i).1, (h₂ i).2.1, fun v hv => (h₂ i).2.2 v (fun h => hv (Finset.mem_union_right _ h))⟩
    · rw [Fin.sum_univ_add]
      simp [Fin.append_left, Fin.append_right]
  | smul c x _ hx =>
    obtain ⟨T, m, f, φ, h, rfl⟩ := hx
    refine ⟨T, m, fun i => c • f i, φ, fun i => ⟨(M.Pol ψ emb).smul_mem c (h i).1, (h i).2⟩, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext x
    simp only [Pi.smul_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.PolKerLieV
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mixedForm_torusTranslate_vacuum_value : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → CayleyRule q n ρ (ω.comp (MonoidHom.inr _ _)) s → ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 → (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) → (∀ x, (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ (ρ x s) = 0) → ∀ (k : Fin (n' / 2)) (t : GU σ n'), t.1.1 = tMat ϖ n' (n' / 2) (Pi.single k 1) → ℓ (ω (1, t) s) = (-1) ^ n * (q : ℂ) ^ (-(n : ℤ)) := by
  first | exact @GlobalTheory.SphTheta.mixed_torus_value | exact GlobalTheory.SphTheta.mixed_torus_value | (intros; apply GlobalTheory.SphTheta.mixed_torus_value <;> assumption)
end
