module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle337
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExactFunctorPhiGammaOfFrames
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAndKernelOfLetterImageTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle329
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases.LiftW

section Gen

variable {O : Type} (LL : Type) [CommRing O] [Field LL] [Algebra O LL]

def basisVec (k : ℕ) (j : Fin k) : ↥(stdG O LL k) :=
  ⟨Pi.single j 1, ⟨Pi.single j 1, by
    funext j'
    simp [Pi.single_apply]⟩⟩

def coordQ (k : ℕ) (j : Fin k) : ((Fin k → LL) ⧸ stdG O LL k) →ₗ[O] (LL ⧸ intO (O := O) LL) :=
  (stdG O LL k).mapQ (intO LL) (LinearMap.proj j) (by
    rintro _ ⟨u, rfl⟩
    exact ⟨u j, rfl⟩)

theorem coordQ_mk (k : ℕ) (j : Fin k) (v : Fin k → LL) :
    coordQ (O := O) LL k j (Submodule.Quotient.mk v) = Submodule.Quotient.mk (v j) := rfl

theorem iotaW_tmul (lam : O) (a k : ℕ) (t : ↥(stdG O LL k)) (s : LL)
    (hs : (Submodule.Quotient.mk s : LL ⧸ intO (O := O) LL) ∈ Xq LL lam a) :
    iotaW LL lam a k (t ⊗ₜ ⟨Submodule.Quotient.mk s, hs⟩) = Submodule.Quotient.mk (s • (t : Fin k → LL)) := rfl

theorem exists_sum (k : ℕ) {X : Type} [AddCommGroup X] [Module O X] (u : ↥(stdG O LL k) ⊗[O] X) :
    ∃ x : Fin k → X, u = ∑ j, basisVec LL k j ⊗ₜ[O] x j := by
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul t y =>
    obtain ⟨_, c, rfl⟩ := t
    refine ⟨fun j => c j • y, ?_⟩
    simp only [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]
    congr 1
    apply Subtype.ext
    funext j'
    simp [basisVec, Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  | add u v hu hv =>
    obtain ⟨x, rfl⟩ := hu
    obtain ⟨y, rfl⟩ := hv
    exact ⟨x + y, by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

theorem coordQ_iotaW (lam : O) (a k : ℕ) (x : Fin k → ↥(Xq LL lam a)) (j : Fin k) :
    coordQ LL k j (iotaW LL lam a k (∑ j', basisVec LL k j' ⊗ₜ[O] x j')) = x j := by
  have h : ∀ j', coordQ LL k j (iotaW LL lam a k (basisVec LL k j' ⊗ₜ[O] x j')) =
      if j = j' then (x j' : LL ⧸ intO (O := O) LL) else 0 := by
    intro j'
    obtain ⟨y, hy⟩ := x j'
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [iotaW_tmul, coordQ_mk]
    by_cases hj : j = j' <;> simp [basisVec, hj]

  simp [map_sum, h]

theorem iotaW_injective (lam : O) (a k : ℕ) : Function.Injective (iotaW LL lam a k) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro u hu
  obtain ⟨x, rfl⟩ := exists_sum LL k u
  have : x = 0 := by
    funext j
    apply Subtype.ext
    rw [← coordQ_iotaW, hu]
    simp
  simp [this]

theorem exists_iotaW (lam : O) (a k : ℕ) (q : (Fin k → LL) ⧸ stdG O LL k) (hq : lam ^ a • q = 0) :
    ∃ u, iotaW LL lam a k u = q := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hx : ∀ j, (Submodule.Quotient.mk (v j) : LL ⧸ intO (O := O) LL) ∈ Xq LL lam a := by
    intro j
    have := congrArg (coordQ LL k j) hq
    rw [map_smul, map_zero, coordQ_mk] at this
    exact this
  refine ⟨∑ j, basisVec LL k j ⊗ₜ[O] ⟨_, hx j⟩, ?_⟩

  simp only [map_sum, iotaW_tmul]
  have : v = ∑ j, v j • (basisVec (O := O) LL k j : Fin k → LL) := by
    funext j'
    simp [basisVec, Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [this]
  exact (map_sum (stdG O LL k).mkQ _ _).symm

variable {LL}

theorem iotaW_actTw (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G]
    (lam : O) (a : ℕ) {k : ℕ} (N : G →* Matrix (Fin k) (Fin k) O) (θ : G →* Oˣ) (g : G)
    (u : ↥(stdG O LL k) ⊗[O] ↥(Xq LL lam a)) :
    iotaW LL lam a k (tableLineDegreeTwo.actTw (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) θ g u) =
      actD (stdLatG hinj N) g (iotaW LL lam a k u) := by
  induction u using TensorProduct.induction_on with
  | zero => exact (congrArg _ (map_zero _)).trans ((map_zero _).trans
      ((congrArg _ (map_zero _)).trans (map_zero _)).symm)
  | add u v hu hv =>
    have e1 := map_add (tableLineDegreeTwo.actTw (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) θ g) u v
    have e2 := map_add (actD (stdLatG hinj N) g) (iotaW LL lam a k u) (iotaW LL lam a k v)
    refine (congrArg _ e1).trans ((map_add _ _ _).trans ?_)
    rw [map_add (f := _)]
    exact (congrArg₂ (· + ·) hu hv).trans e2.symm
  | tmul t y =>
    obtain ⟨y, hy⟩ := y
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine (map_smul (iotaW LL lam a k) (((θ g)⁻¹ : Oˣ) : O)
      ((show ↥(stdG O LL k) from actT (stdLatG hinj (twistM N θ)) g t) ⊗ₜ[O] ⟨Submodule.Quotient.mk s, hy⟩)).trans ?_
    rw [iotaW_tmul, iotaW_tmul, ← Submodule.Quotient.mk_smul]
    refine congrArg Submodule.Quotient.mk ?_
    show (((θ g)⁻¹ : Oˣ) : O) • s • (((((θ g : Oˣ) : O) • N g).map (algebraMap O LL)).mulVec (t : Fin k → LL)) =
      ((N g).map (algebraMap O LL)).mulVec (s • (t : Fin k → LL))
    have e : (((θ g : Oˣ) : O) • N g).map (algebraMap O LL) = ((θ g : Oˣ) : O) • (N g).map (algebraMap O LL) := by
      ext p q
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
      rw [Algebra.smul_def]
    rw [e, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_comm s, smul_smul, Units.inv_mul, one_smul]

theorem exists_twistedCocycle_lift_torsion (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (lam : O) (a : ℕ) {k : ℕ} (N : G →* Matrix (Fin k) (Fin k) O) (θ : G →* Oˣ)
    (f : G → (Fin k → LL) ⧸ stdG O LL k) (hf : f ∈ divisibleCocycles (stdLatG hinj N)) (hk : ∀ g, lam ^ a • f g = 0) :
    ∃ z' : G → ↥(stdLatG hinj (twistM N θ)).T ⊗[O] ↥(Xq LL lam a),
      tableLineDegreeTwo.IsCoc (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) θ z' ∧ ∀ g, iotaW LL lam a k (z' g) = f g := by
  choose z hz using fun g => exists_iotaW LL lam a k (f g) (hk g)
  refine ⟨z, ⟨?_, fun g h => ?_⟩, hz⟩
  · refine IsLocallyConstant.desc z (iotaW LL lam a k) ?_ (iotaW_injective LL lam a k)
    have : (iotaW LL lam a k) ∘ z = f := funext hz
    rw [this]
    exact hf.1
  · apply iotaW_injective LL lam a k
    refine (hz _).trans ((hf.2 g h).trans ?_)
    refine Eq.trans ?_ (map_add (iotaW LL lam a k) (z g) _).symm
    rw [hz g, ← hz h]
    exact congrArg _ (iotaW_actTw hinj lam a N θ g (z h)).symm

theorem lift_gen (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (lam : O) (a : ℕ) {k : ℕ} (N : G →* Matrix (Fin k) (Fin k) O) (θ χ : G →* Oˣ) (hχ : χ = θ)
    (f : G → (Fin k → LL) ⧸ stdG O LL k) (hf : f ∈ divisibleCocycles (stdLatG hinj N)) (hk : ∀ g, lam ^ a • f g = 0) :
    ∃ z' : G → ↥(stdLatG hinj (twistM N θ)).T ⊗[O] ↥(Xq LL lam a),
      tableLineDegreeTwo.IsCoc (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) χ z' ∧ ∀ g, iotaW LL lam a k (z' g) = f g := by
  subst hχ
  exact exists_twistedCocycle_lift_torsion hinj lam a N χ f hf hk

end Gen

theorem chiT_one {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) : chiT C θ 1 = θ := by
  ext g
  simp [chiT, chiOC]

theorem lift_cocycle : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ)
      (f : Br.G D.nbr i w hw → (Fin k → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 k),
    f ∈ divisibleCocycles (latC C N) → (∀ g, lam ^ a • f g = 0) →
    ∃ z' : Br.G D.nbr i w hw → ↥(latC C (twistM N θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a),
      tableLineDegreeTwo.IsCoc (latC C (twistM N θ)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' ∧ ∀ g, iotaW ↥C.LL.1 lam a k (z' g) = f g := by
  intro D i w hw C lam _ k N θ a f hf hk
  exact lift_gen Subtype.val_injective lam a N θ (chiT C θ 1) (chiT_one C θ) f hf hk

end GlobalTheory.UseLoc.Cases.LiftW

end
end

section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

noncomputable section
namespace GlobalTheory.UseLoc.Cases

section Gen1
variable {O : Type} [CommRing O]

def evOneQ (LL : Type) [Field LL] [Algebra O LL] : ((Fin 1 → LL) ⧸ stdG O LL 1) →ₗ[O] (LL ⧸ intO (O := O) LL) :=
  (stdG O LL 1).mapQ (intO (O := O) LL) (LinearMap.proj (R := O) (φ := fun _ : Fin 1 => LL) 0) (by
    rintro _ ⟨u, rfl⟩
    exact ⟨u 0, rfl⟩)

variable {LL : Type} [Field LL] [Algebra O LL]

theorem evOneQ_mk (v : Fin 1 → LL) :
    evOneQ (O := O) LL (Submodule.Quotient.mk v) = Submodule.Quotient.mk (v 0) := rfl

theorem evOneQ_mem {lam : O} {a : ℕ} {q : (Fin 1 → LL) ⧸ stdG O LL 1} (h : lam ^ a • q = 0) :
    evOneQ LL q ∈ Xq LL lam a := by
  show (lam ^ a • (LinearMap.id : (LL ⧸ intO (O := O) LL) →ₗ[O] _)) (evOneQ LL q) = 0
  rw [LinearMap.smul_apply, LinearMap.id_apply, ← map_smul, h, map_zero]

def oneO : ↥(intO (O := O) LL) := ⟨1, 1, map_one (algebraMap O LL)⟩

theorem iotaC_oneO (lam : O) (a : ℕ) (q : (Fin 1 → LL) ⧸ stdG O LL 1) (h : evOneQ LL q ∈ Xq LL lam a) :
    iotaC LL lam a (oneO ⊗ₜ ⟨evOneQ LL q, h⟩) = q := by
  induction q using Submodule.Quotient.induction_on with
  | H v =>
    show iotaG (intO LL) (stdG O LL 1) (constOne LL) (constOne_mem LL) (oneO ⊗ₜ (evOneQ LL (Submodule.Quotient.mk v))) = _
    rw [evOneQ_mk, iotaG_tmul]
    congr 1
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp [constOne, oneO]

def oneT (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] (ψ : G →* Oˣ) : ↥(latOne hinj ψ).T :=
  oneO

theorem actT_latOne_oneT (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] (ψ : G →* Oˣ) (g : G) :
    actT (latOne hinj ψ) g (oneT hinj ψ) = ((ψ g : Oˣ) : O) • oneT hinj ψ := by
  apply Subtype.ext
  show ((tableLineDegreeTwo.charL (LL := LL) ψ g : LLˣ) : LL) • (1 : LL) = ((ψ g : Oˣ) : O) • (1 : LL)
  simp [tableLineDegreeTwo.charL, Algebra.smul_def]

end Gen1

section Gen2
variable {O : Type} [CommRing O] {LL : Type} [Field LL] [Algebra O LL]

theorem actTw_oneO (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (X : Type) [AddCommGroup X] [Module O X] (χ ψ : G →* Oˣ) (g : G) (x : X) :
    tableLineDegreeTwo.actTw (latOne hinj ψ) X χ g (oneT hinj ψ ⊗ₜ x) = oneT hinj ψ ⊗ₜ ((((χ g)⁻¹ * ψ g : Oˣ) : O) • x) := by
  rw [tableLineDegreeTwo.actTw, LinearMap.smul_apply, LinearMap.rTensor_tmul, actT_latOne_oneT, TensorProduct.smul_tmul,
    ← TensorProduct.tmul_smul, Units.val_mul, mul_smul]

theorem evOneQ_actD (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (N : G →* Matrix (Fin 1) (Fin 1) O) (g : G) (q : (Fin 1 → LL) ⧸ stdG O LL 1) :
    evOneQ LL (actD (stdLatG hinj N) g q) = N g 0 0 • evOneQ LL q := by
  induction q using Submodule.Quotient.induction_on with
  | H v =>
    show evOneQ LL (Submodule.Quotient.mk (matRep (mapM (algebraMap O LL) N) g v)) = _
    rw [evOneQ_mk, evOneQ_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    simp [matRep, mapM, Matrix.mulVec, dotProduct, Algebra.smul_def]

end Gen2

section Gen3
variable {O : Type} [CommRing O] {LL : Type} [Field LL] [Algebra O LL]

theorem liftC_gen (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (N : G →* Matrix (Fin 1) (Fin 1) O) (χ ψ : G →* Oˣ) (hN : ∀ g, (((χ g)⁻¹ * ψ g : Oˣ) : O) = N g 0 0)
    (lam : O) (a : ℕ) (f : G → (Fin 1 → LL) ⧸ stdG O LL 1) (hf : f ∈ divisibleCocycles (stdLatG hinj N))
    (htor : ∀ g, lam ^ a • f g = 0) :
    ∃ z' : G → ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a),
      tableLineDegreeTwo.IsCoc (latOne hinj ψ) ↥(Xq LL lam a) χ z' ∧ ∀ g, iotaC LL lam a (z' g) = f g := by
  classical
  obtain ⟨hlc, hco⟩ := hf
  let F : ((Fin 1 → LL) ⧸ stdG O LL 1) → ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a) :=
    fun q => if hq : lam ^ a • q = 0 then oneT hinj ψ ⊗ₜ ⟨evOneQ LL q, evOneQ_mem hq⟩ else 0
  refine ⟨fun g => oneT hinj ψ ⊗ₜ ⟨evOneQ LL (f g), evOneQ_mem (htor g)⟩, ⟨?_, ?_⟩, ?_⟩
  · have hF : (fun g => oneT hinj ψ ⊗ₜ[O]
        (⟨evOneQ LL (f g), evOneQ_mem (htor g)⟩ : ↥(Xq LL lam a))) = F ∘ f := by
      funext g
      simp only [F, Function.comp_apply, dif_pos (htor g)]
    rw [hF]
    exact hlc.comp F
  · intro g h
    beta_reduce
    rw [actTw_oneO, ← TensorProduct.tmul_add]
    congr 1
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul]
    rw [hco g h, hN g]
    exact ((evOneQ LL).map_add _ _).trans (congrArg (evOneQ LL (f g) + ·) (evOneQ_actD hinj N g (f h)))
  · intro g
    exact iotaC_oneO lam a (f g) _

end Gen3

section AtW
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem locOC_chiRatO_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (c : ℕ) (g : Br.G D.nbr i w hw) :
    locOC C (chiRatO D.nd i c) g 0 0 =
      ((chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) := by
  simp [locOC, chiOC, Br.locO, Br.iota, mapM, chiRatO, twistM]

theorem chiT_one_eq_theta (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) : chiT C θ 1 = θ := by
  simp [chiT, chiOC]

theorem chiT_ratio (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ)
    (g : Br.G D.nbr i w hw) :
    (((chiT C θ 1 g)⁻¹ * chiT C θ c g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) = locOC C (chiRatO D.nd i c) g 0 0 := by
  rw [locOC_chiRatO_apply, chiT_one_eq_theta]
  congr 1
  simp only [chiT, MonoidHom.mul_apply]
  rw [mul_comm, mul_assoc, mul_inv_cancel, mul_one]

end AtW

theorem liftC_main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c a : ℕ) (f : Br.G D.nbr i w hw → (Fin 1 → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 1),
    f ∈ divisibleCocycles (latC C (locOC C (chiRatO D.nd i c))) → (∀ g, lam ^ a • f g = 0) →
    ∃ z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a),
      tableLineDegreeTwo.IsCoc (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' ∧
      ∀ g, iotaC ↥C.LL.1 lam a (z' g) = f g := by
  intro D i w hw C lam _ θ c a f hf htor
  exact liftC_gen Subtype.val_injective (locOC C (chiRatO D.nd i c)) (chiT C θ 1) (chiT C θ c) (chiT_ratio C θ c)
    lam a f hf htor

end GlobalTheory.UseLoc.Cases

end
end

section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases.ReadC

section Gen
variable {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] {G : Type} [Group G]

theorem actT_latOne (hinj : Function.Injective (algebraMap O LL)) (ψ : G →* Oˣ) (g : G) :
    Formalism.WeaklyAdmissibleFiltrations.actT (latOne hinj ψ) g = ((ψ g : Oˣ) : O) • LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x, hx⟩
  apply Subtype.ext
  simp only [Formalism.WeaklyAdmissibleFiltrations.actT, LinearMap.restrict_apply, LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul]
  show ((tableLineDegreeTwo.charL (LL := LL) ψ g : LLˣ) : LL) • x = ((ψ g : Oˣ) : O) • x
  simp [tableLineDegreeTwo.charL, Algebra.smul_def]

theorem actTw_latOne (hinj : Function.Injective (algebraMap O LL)) (lam : O) (a : ℕ) (ψ χ : G →* Oˣ) (g : G) :
    tableLineDegreeTwo.actTw (latOne hinj ψ) (Xq LL lam a) χ g = (((χ g)⁻¹ * ψ g : Oˣ) : O) • LinearMap.id := by
  rw [tableLineDegreeTwo.actTw, actT_latOne, LinearMap.rTensor_smul, LinearMap.rTensor_id, smul_smul, Units.val_mul]

theorem actD_one (hinj : Function.Injective (algebraMap O LL)) (M : G →* Matrix (Fin 1) (Fin 1) O) (g : G) :
    actD (stdLatG hinj M) g = M g 0 0 • LinearMap.id := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.smul_apply, LinearMap.id_apply, actD,
    ← Submodule.Quotient.mk_smul]
  erw [Submodule.mapQ_apply]
  congr 1
  funext j
  fin_cases j
  simp [stdLatG, matRep, mapM, Matrix.mulVec, dotProduct, Algebra.smul_def]

theorem equivG (hinj : Function.Injective (algebraMap O LL)) (lam : O) (a : ℕ) (ψ χ : G →* Oˣ)
    (M : G →* Matrix (Fin 1) (Fin 1) O) (hM : ∀ g, M g 0 0 = (((χ g)⁻¹ * ψ g : Oˣ) : O)) (g : G)
    (u : ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a)) :
    iotaC LL lam a (tableLineDegreeTwo.actTw (latOne hinj ψ) (Xq LL lam a) χ g u) =
      actD (stdLatG hinj M) g (iotaC LL lam a u) := by
  have h1 : tableLineDegreeTwo.actTw (latOne hinj ψ) (Xq LL lam a) χ g u = (((χ g)⁻¹ * ψ g : Oˣ) : O) • u := by
    rw [actTw_latOne]; rfl
  rw [h1, actD_one, hM]
  exact (iotaC LL lam a).map_smul _ u

end Gen
end GlobalTheory.UseLoc.Cases.ReadC

namespace GlobalTheory.UseLoc.Cases.ReadC
section Gen2
variable {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] {G : Type} [Group G]

theorem readG (hinj : Function.Injective (algebraMap O LL)) (lam : O) (a : ℕ) (ψ χ : G →* Oˣ)
    (M : G →* Matrix (Fin 1) (Fin 1) O) (hM : ∀ g, M g 0 0 = (((χ g)⁻¹ * ψ g : Oˣ) : O))
    (z' : G → ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a))
    (hz : tableLineDegreeTwo.IsCob (latOne hinj ψ) ↥(Xq LL lam a) χ z') :
    (fun g => iotaC LL lam a (z' g)) ∈ BD (stdLatG hinj M) := by
  obtain ⟨m, hm⟩ := hz
  refine ⟨iotaC LL lam a m, ?_⟩
  funext g
  have key := equivG hinj lam a ψ χ M hM g m
  rw [hm g]
  refine Eq.trans ?_ ((iotaC LL lam a).map_sub _ m).symm
  exact (congrArg (fun y => y - iotaC LL lam a m) key).symm

end Gen2
end GlobalTheory.UseLoc.Cases.ReadC

namespace GlobalTheory.UseLoc.Cases.ReadC

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem entry (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (c : ℕ) (g : Br.G D.nbr i w hw) :
    locOC C (chiRatO D.nd i c) g 0 0 = ((chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) := by
  simp [locOC, chiOC, Br.locO, mapM, chiRatO, twistM, Br.iota]

theorem ratio (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ) (g : Br.G D.nbr i w hw) :
    (chiT C θ 1 g)⁻¹ * chiT C θ c g = chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g := by
  have h1 : chiOC C 1 g = 1 := by simp [chiOC]
  simp only [chiT, MonoidHom.mul_apply, mul_inv_cancel, h1, one_mul]
  rw [mul_comm (chiOC C _ g) (θ g)]
  exact inv_mul_cancel_left _ _

theorem entry_ratio (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ) (g : Br.G D.nbr i w hw) :
    locOC C (chiRatO D.nd i c) g 0 0 = (((chiT C θ 1 g)⁻¹ * chiT C θ c g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) := by
  rw [entry, ratio]

end GlobalTheory.UseLoc.Cases.ReadC

theorem GlobalTheory.UseLoc.Cases.readC_cob : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c a : ℕ)
    (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsCob (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (fun g => iotaC ↥C.LL.1 lam a (z' g)) ∈ BD (latC C (locOC C (chiRatO D.nd i c))) :=
  fun D i w hw C lam θ c a z' hz =>
    ReadC.readG (LL := ↥C.LL.1) Subtype.val_injective lam a (chiT C θ c) (chiT C θ 1) (locOC C (chiRatO D.nd i c))
      (ReadC.entry_ratio C θ c) z' hz
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

theorem _root_.GlobalTheory.T.exists_exact_functor_phiGamma_of_frames : ∀ {k G : Type} [Field k] [Group G] {Rk : Type} [CommRing Rk] [Algebra k Rk] {l n : ℕ} [NeZero n] (R : RingPG k l) (κ : k⸨X⸩ →+* Rk) (φ : Rk →ₐ[k] Rk) (a : G → (Rk →ₐ[k] Rk)) (g₀ : G) (ε : ZMod n → Rk) (Obj : Ob k G → Prop) (β : ∀ A : Ob k G, ZMod n → (Vc k A.m →+ Rk ⊗[k] (Fin A.m → k))), IsFrames R κ φ a g₀ ε Obj β → ∃ F : DFun R n G, F.Obj = Obj ∧ (∀ A, Obj A → ∀ i x, β A i ((F.D A).φ i x) = Phi φ A.m (β A (i - 1) x)) ∧ (∀ A, Obj A → ∀ i x, β A i ((F.D A).γ i x) = Act a A g₀ (β A i x)) ∧ (∀ A B f, Obj A → Obj B → IsHom A B f → ∀ i x, β B i (F.map A B f i x) = f.baseChange Rk (β A i x)) ∧ ∀ i, β (chr 1) i (F.unit i) = ε i ⊗ₜ[k] (fun _ => 1) := by
  first | exact @GlobalTheory.RedFun.exists_dfun_of_frames | exact GlobalTheory.RedFun.exists_dfun_of_frames | (intros; apply GlobalTheory.RedFun.exists_dfun_of_frames <;> assumption)
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

theorem _root_.GlobalTheory.T.finrank_and_kernel_of_letter_image_tensor : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA} (E : EtTie W RA RW inclR φR gR πA) {k : Type} [Field k] [Algebra O k] {Rk : Type} [CommRing Rk] [Algebra k Rk] [Algebra O Rk] [IsScalarTower O k Rk] (ρ : RW →ₐ[O] Rk) (lam : O) (κ : k⸨X⸩ →+* Rk), IsRed E ρ (k := k) lam κ → ∀ (T : LocLat G Qp LL O) (m : ℕ) (q : ↥T.L.T →ₗ[O] (Fin m → k)), Function.Surjective q → ∀ (T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), (∀ x : ↥T.L.T, q x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x) → ∀ i, (∃ u : Fin m → W.DD T, ∀ x, ∃ c : Fin m → k⸨X⸩, eps E ρ i • J E ρ T q x = ∑ j, κ (c j) • eps E ρ i • J E ρ T q (u j)) ∧ ∀ h : LatHom T.L T'.L, (∀ x, f.f (h.f x) = algebraMap O LL lam • x) → ∀ x, eps E ρ i • J E ρ T q x = 0 → ∃ y, W.map f y = (letE i : LetA O n) • x := by
  first | exact @GlobalTheory.RedDim.dim_ker | exact GlobalTheory.RedDim.dim_ker | (intros; apply GlobalTheory.RedDim.dim_ker <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.teichmullerEpsilonRoots_mem_frobeniusPerfection_mod_l : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), ∀ u ∈ Subring.closure (Set.range AI.εroot ∪ {xb | ∃ c : Om l, c ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ c ^ m = 1 ∧ IsTiltOf c m xb}), ∃ (n : ℕ) (e : W.EE) (r : RW LL), (φRW LL)^[n] ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (WittVector.teichmuller l u)) = E.tie.ioE e + (l : RW LL) * r := by
  first | exact @GlobalTheory.DecomplPerf.teich_mem_perfection | exact GlobalTheory.DecomplPerf.teich_mem_perfection | (intros; apply GlobalTheory.DecomplPerf.teich_mem_perfection <;> assumption)
end
