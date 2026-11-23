module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle917
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)
open GlobalTheory.ThetaTransform

attribute [local instance] Formalism.BasicNotions.Host.cmStar




theorem GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps : ∀ (D : D7) (m n N : ℕ) (e : Matrix (Fin m) (Fin n) (AE D) ≃ₗ[AF D.host.F] VA D.host.F N), (∀ x : Matrix (Fin m) (Fin n) D.host.E, ∃ y z : Fin N → D.host.F, e (incM D.host.F x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) → ∀ y z : Fin N → D.host.F, ∃ x : Matrix (Fin m) (Fin n) D.host.E, e (incM D.host.F x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := by
  intro D m n N e hrat y z
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  let I : Matrix (Fin m) (Fin n) D.host.E →ₗ[D.host.F] Matrix (Fin m) (Fin n) (AE D) :=
    (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).toLinearMap.mapMatrix
  have hI : ∀ x, I x = incM D.host.F x := fun x => rfl
  let L : Matrix (Fin m) (Fin n) D.host.E →ₗ[D.host.F] VA D.host.F N := (e.toLinearMap.restrictScalars D.host.F).comp I
  have hL : ∀ x, L x = e (incM D.host.F x) := fun x => rfl
  let r : (Fin N → D.host.F) →ₗ[D.host.F] (Fin N → AF D.host.F) :=
    LinearMap.pi fun i => (Algebra.linearMap D.host.F (AF D.host.F)).comp (LinearMap.proj i)
  let R : ((Fin N → D.host.F) × (Fin N → D.host.F)) →ₗ[D.host.F] VA D.host.F N := LinearMap.prodMap r r
  have hR : ∀ y z, R (y, z) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := fun _ _ => rfl
  have hAinj : Function.Injective (algebraMap D.host.F (AF D.host.F)) := AdeleRing.algebraMap_injective _ _
  have hrinj : Function.Injective r := fun a b h => funext fun i => hAinj (congrFun h i)
  have hRinj : Function.Injective R := fun a b h => Prod.ext (hrinj (congrArg Prod.fst h)) (hrinj (congrArg Prod.snd h))
  have hIinj : Function.Injective I := fun a b h => Matrix.ext fun i j =>
    Algebra.TensorProduct.includeRight_injective hAinj (congrFun (congrFun h i) j)
  have hLinj : Function.Injective L := e.injective.comp hIinj
  have hle : LinearMap.range L ≤ LinearMap.range R := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y', z', h⟩ := hrat x
    exact ⟨(y', z'), by rw [hR, hL, h]⟩
  have hdim : Fintype.card (Fin m) * Fintype.card (Fin n) * Module.finrank D.host.F D.host.E = N + N := by
    have h1 := e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fin_fun] at h1
    exact h1
  have hfin : Module.finrank D.host.F (LinearMap.range L) = Module.finrank D.host.F (LinearMap.range R) := by
    rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hRinj, Module.finrank_matrix,
      Module.finrank_prod, Module.finrank_fin_fun, hdim]
  have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
  obtain ⟨x, hx⟩ : (R (y, z)) ∈ LinearMap.range L := heq ▸ ⟨(y, z), rfl⟩
  exact ⟨x, by rw [← hL, hx, hR]⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)
open GlobalTheory.ThetaTransform

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicCoord

section Ad

variable (F : Type) [Field F] [NumberField F]

theorem fstA_pairA (x : Ainf F) (y : Af F) : fstA F (pairA F x y) = x := rfl

theorem sndA_pairA (x : Ainf F) (y : Af F) : sndA F (pairA F x y) = y := rfl

variable {F} in
theorem af_ext {a b : AF F} (h1 : fstA F a = fstA F b) (h2 : sndA F a = sndA F b) : a = b :=
  Prod.ext (α := Ainf F) (β := Af F) h1 h2

theorem pairA_mul_eq_zero_iff_snd (a : AF F) : pairA F 0 1 * a = 0 ↔ sndA F a = 0 := by
  constructor
  · intro h
    have := congrArg (sndA F) h
    rwa [map_mul, map_zero, sndA_pairA, one_mul] at this
  · intro h
    refine af_ext ?_ ?_
    · rw [map_mul, map_zero, fstA_pairA, zero_mul]
    · rw [map_mul, map_zero, sndA_pairA, h, mul_zero]

theorem pairA_mul_eq_zero_iff_fst (a : AF F) : pairA F 1 0 * a = 0 ↔ fstA F a = 0 := by
  constructor
  · intro h
    have := congrArg (fstA F) h
    rwa [map_mul, map_zero, fstA_pairA, one_mul] at this
  · intro h
    refine af_ext ?_ ?_
    · rw [map_mul, map_zero, fstA_pairA, h, mul_zero]
    · rw [map_mul, map_zero, sndA_pairA, zero_mul]

def incF : Af F →ₗ[F] AF F where
  toFun y := pairA F 0 y
  map_add' y y' := af_ext (by rw [map_add (f := _), fstA_pairA, fstA_pairA, fstA_pairA, add_zero])
    (by rw [map_add (f := _), sndA_pairA, sndA_pairA, sndA_pairA])
  map_smul' c y := af_ext (by rw [map_smul, fstA_pairA, fstA_pairA, RingHom.id_apply, smul_zero])
    (by rw [map_smul, sndA_pairA, sndA_pairA, RingHom.id_apply])

def incI : Ainf F →ₗ[F] AF F where
  toFun y := pairA F y 0
  map_add' y y' := af_ext (by rw [map_add (f := _), fstA_pairA, fstA_pairA, fstA_pairA])
    (by rw [map_add (f := _), sndA_pairA, sndA_pairA, sndA_pairA, add_zero])
  map_smul' c y := af_ext (by rw [map_smul, fstA_pairA, fstA_pairA, RingHom.id_apply])
    (by rw [map_smul, sndA_pairA, sndA_pairA, RingHom.id_apply, smul_zero])

theorem incF_sndA (a : AF F) : incF F (sndA F a) = pairA F 0 1 * a :=
  af_ext (by rw [map_mul, fstA_pairA, zero_mul]; rfl) (by rw [map_mul, sndA_pairA, one_mul]; rfl)

theorem incI_fstA (a : AF F) : incI F (fstA F a) = pairA F 1 0 * a :=
  af_ext (by rw [map_mul, fstA_pairA, one_mul]; rfl) (by rw [map_mul, sndA_pairA, zero_mul]; rfl)

end Ad

variable (D : D7)

def secF : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D := TensorProduct.map (incF D.host.F) LinearMap.id

def secI : Ainf D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D := TensorProduct.map (incI D.host.F) LinearMap.id

theorem secF_finPart (z : AE D) : secF D (finPart D z) = pairA D.host.F 0 1 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [(finPart D).map_zero, (secF D).map_zero, smul_zero]
  | tmul a b =>
    have h1 : finPart D (a ⊗ₜ b) = sndA D.host.F a ⊗ₜ b := rfl
    rw [h1, secF, TensorProduct.map_tmul, LinearMap.id_apply, incF_sndA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [map_add (finPart D), map_add (secF D), hx, hy, smul_add]

theorem secI_infPart (z : AE D) : secI D (infPart D z) = pairA D.host.F 1 0 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [(infPart D).map_zero, (secI D).map_zero, smul_zero]
  | tmul a b =>
    have h1 : infPart D (a ⊗ₜ b) = fstA D.host.F a ⊗ₜ b := rfl
    rw [h1, secI, TensorProduct.map_tmul, LinearMap.id_apply, incI_fstA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [map_add (infPart D), map_add (secI D), hx, hy, smul_add]

theorem finPart_smul (z : AE D) : finPart D (pairA D.host.F 0 1 • z) = finPart D z := by
  rw [Algebra.smul_def, (finPart D).map_mul]
  have : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show sndA D.host.F (algebraMap (AF D.host.F) (AF D.host.F) (pairA D.host.F 0 1)) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, sndA_pairA]
    rfl
  rw [this, one_mul]

theorem infPart_smul (z : AE D) : infPart D (pairA D.host.F 1 0 • z) = infPart D z := by
  rw [Algebra.smul_def, (infPart D).map_mul]
  have : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show fstA D.host.F (algebraMap (AF D.host.F) (AF D.host.F) (pairA D.host.F 1 0)) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, fstA_pairA]
    rfl
  rw [this, one_mul]

theorem finPart_eq_zero_iff (z : AE D) : finPart D z = 0 ↔ pairA D.host.F 0 1 • z = 0 := by
  constructor
  · intro h; rw [← secF_finPart, h, (secF D).map_zero]
  · intro h; rw [← finPart_smul, h, (finPart D).map_zero]

theorem infPart_eq_zero_iff (z : AE D) : infPart D z = 0 ↔ pairA D.host.F 1 0 • z = 0 := by
  constructor
  · intro h; rw [← secI_infPart, h, (secI D).map_zero]
  · intro h; rw [← infPart_smul, h, (infPart D).map_zero]

theorem smul_vec_fin {N : ℕ} (u : Fin N → AF D.host.F) : pairA D.host.F 0 1 • u = 0 ↔ GlobalTheory.SWQ.fin u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_snd D.host.F (u l)

theorem smul_vec_inf {N : ℕ} (u : Fin N → AF D.host.F) : pairA D.host.F 1 0 • u = 0 ↔ GlobalTheory.SWQ.inf u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_fst D.host.F (u l)

theorem smul_pair_eq_zero {N : ℕ} (c : AF D.host.F) (w : VA D.host.F N) : c • w = 0 ↔ c • w.1 = 0 ∧ c • w.2 = 0 :=
  Prod.ext_iff

theorem coord (D : D7) (m n N : ℕ) (e : Matrix (Fin m) (Fin n) (AE D) ≃ₗ[AF D.host.F] VA D.host.F N) :
    Continuous e ∧ Continuous e.symm ∧
      (∀ x, x.map (finPart D) = 0 ↔ GlobalTheory.SWQ.fin (e x).1 = 0 ∧ GlobalTheory.SWQ.fin (e x).2 = 0) ∧
      (∀ x, x.map (infPart D) = 0 ↔ GlobalTheory.SWQ.inf (e x).1 = 0 ∧ GlobalTheory.SWQ.inf (e x).2 = 0) := by
  haveI h0 : IsModuleTopology (AF D.host.F) (AE D) := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop
  haveI h1 : IsModuleTopology (AF D.host.F) (Fin n → AE D) := IsModuleTopology.instPi
  haveI h2 : IsModuleTopology (AF D.host.F) (Matrix (Fin m) (Fin n) (AE D)) := IsModuleTopology.instPi
  refine ⟨IsModuleTopology.continuous_of_linearMap e.toLinearMap,
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap, fun x => ?_, fun x => ?_⟩
  · have key : x.map (finPart D) = 0 ↔ pairA D.host.F 0 1 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => finPart_eq_zero_iff D (x i j)
    rw [key, ← smul_vec_fin, ← smul_vec_fin, ← smul_pair_eq_zero, ← LinearEquiv.map_smul,
      LinearEquiv.map_eq_zero_iff]
  · have key : x.map (infPart D) = 0 ↔ pairA D.host.F 1 0 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => infPart_eq_zero_iff D (x i j)
    rw [key, ← smul_vec_inf, ← smul_vec_inf, ← smul_pair_eq_zero, ← LinearEquiv.map_smul,
      LinearEquiv.map_eq_zero_iff]

end GlobalTheory.AdelicCoord

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodingerHerm

theorem sesq_apply (D : D7) {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) (x y : Fin k → D.host.E) :
    GlobalTheory.WeilSchrodinger.sesq D G x y = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [GlobalTheory.WeilSchrodinger.sesq, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply,
    smul_eq_mul, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem sesq_transpose_eq_form (D : D7) {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E) (x y : Fin k → D.host.E) :
    GlobalTheory.WeilSchrodinger.sesq D Jᵀ y x = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig J x y := by
  rw [sesq_apply, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  rfl

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s) :
    M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let P : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : Pᵀ * M * P.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_neg,
    Matrix.det_one, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0, mul_zero, zero_mul] at hd
  rw [Fintype.card_fin, one_mul, mul_one] at hd
  exact pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) hd.symm

variable (D : D7) (B : Base D.host.F D.host.E) {n : ℕ} (X : Spc D.host.F D.host.E n) {r s : ℕ}

theorem det_J_ne_zero (hX : X.IsHerm D.sp.cm.sig B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have h := det_ne_zero_of_hasSig (hX.sig w)
  intro h0
  apply h
  have hm : (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det := (RingHom.map_det _ _).symm
  rw [hm, h0, map_zero]

theorem mem_one_iff (z : D.host.E) : z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) ↔ IsIntegral ℤ z := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨o, rfl⟩
    exact o.isIntegral_coe
  · intro h
    exact ⟨⟨z, h⟩, rfl⟩

theorem herm_nondeg_unimod (hX : X.IsHerm D.sp.cm.sig B r s) :
    (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).IsSymm ∧ (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).Nondegenerate ∧
      Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ) X.L := by
  have hdet : X.Jᵀ.det ≠ 0 := by rw [Matrix.det_transpose]; exact det_J_ne_zero D B X hX
  refine ⟨⟨fun x y => ?_⟩, ⟨fun x hx => ?_, fun y hy => ?_⟩, ?_⟩
  ·
    have hs : ∀ i j, star (X.J i j) = X.J j i := fun i j => hX.herm j i
    simp only [sesq_apply, starRingEnd_apply, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star,
      Pi.star_apply, Matrix.transpose_apply, hs, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  ·
    have h1 : star x ᵥ* X.Jᵀ = 0 := by
      refine dotProduct_eq_zero _ fun v => ?_
      rw [← Matrix.dotProduct_mulVec, ← sesq_apply]
      exact hx v
    have h2 : star x = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet h1
    simpa using congrArg star h2
  ·
    have h1 : X.Jᵀ *ᵥ y = 0 := by
      refine dotProduct_eq_zero _ fun v => ?_
      rw [dotProduct_comm]
      have := hy (star v)
      rwa [sesq_apply, star_star] at this
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet h1
  ·
    show Formalism.E.hdual _ X.L = X.L
    ext x
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
    rw [hX.dual x]
    refine forall₂_congr fun y _ => ?_
    rw [sesq_transpose_eq_form, mem_one_iff]

end GlobalTheory.WeilSchrodingerHerm

end

theorem GlobalTheory.WeilSchrodingerHerm.main : ∀ (D : D7) (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (n : ℕ) (X : Spc D.host.F D.host.E n) (r s : ℕ), X.IsHerm D.sp.cm.sig B r s →
      (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).IsSymm ∧ (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).Nondegenerate ∧
        Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ) X.L :=
  fun D B _ _ X _ _ hX => GlobalTheory.WeilSchrodingerHerm.herm_nondeg_unimod D B X hX
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_smoothMatInf_ne_zero_at_one : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ)
    (W : GL (Fin n) (Cinf E) → ℂ), Continuous W → W 1 ≠ 0 →
    ∃ α : (Fin n → Fin n → Cinf E) → ℂ, ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧
      tsupport α ⊆ {x | IsUnit (Matrix.of x)} ∧ smoothMatInf α W 1 ≠ 0 := by
  intro E _ _ n W hW h1
  have hemb : Topology.IsOpenEmbedding (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E))) := by
    open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) (Cinf E))
  have hS0 : IsOpen {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} := by
    have e : {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} =
        Set.range (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E))) :=
      Set.ext fun x => ⟨fun ⟨u, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, hu⟩⟩
    rw [e]; exact hemb.isOpen_range
  have hGL : ContinuousOn (fun x : Fin n → Fin n → Cinf E => toGLInf (Matrix.of x)) {x | IsUnit (Matrix.of x)} := by
    rw [hemb.isInducing.continuousOn_iff]
    exact continuousOn_id.congr fun x hx => val_toGLInf hx
  set S : Set (Fin n → Fin n → Cinf E) := {x | IsUnit (Matrix.of x)} with hSdef
  have hS : IsOpen S := hS0
  have hF : ContinuousOn (fun x : Fin n → Fin n → Cinf E => onMatInf W (Matrix.of x)) S := by
    refine (hW.comp_continuousOn hGL).congr fun x hx => ?_
    exact onMatInf_of_isUnit W hx
  set c : ℂ := starRingEnd ℂ (W 1) with hc
  set U : Set (Fin n → Fin n → Cinf E) := S ∩ (fun x => (c * onMatInf W (Matrix.of x)).re) ⁻¹' Set.Ioi 0 with hUdef
  have hU : IsOpen U :=
    (Complex.continuous_re.comp_continuousOn (continuousOn_const.mul hF)).isOpen_inter_preimage hS isOpen_Ioi
  set x0 : Fin n → Fin n → Cinf E := fun i j => (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j with hx0def
  have hx0 : Matrix.of x0 = 1 := by ext i j; rfl
  have hval : onMatInf W (Matrix.of x0) = W 1 := by
    rw [hx0]; simpa using onMatInf_val W 1
  have hpos : 0 < (c * W 1).re := by
    rw [hc, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_pos.2 h1
  have hx0U : x0 ∈ U := by
    refine ⟨?_, ?_⟩
    · show IsUnit (Matrix.of x0); rw [hx0]; exact isUnit_one
    · show 0 < (c * onMatInf W (Matrix.of x0)).re; rw [hval]; exact hpos
  obtain ⟨ρ, h1ρ, h2ρ, h3ρ, h4ρ, h5ρ⟩ := exists_contDiff_tsupport_subset (n := ⊤) (hU.mem_nhds hx0U)
  have hts : tsupport (fun x => (ρ x : ℂ)) ⊆ U :=
    (tsupport_comp_subset (g := fun r : ℝ => (r : ℂ)) (by simp) ρ).trans h1ρ
  have hcs : HasCompactSupport (fun x => (ρ x : ℂ)) := h2ρ.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨fun x => (ρ x : ℂ), Complex.ofRealCLM.contDiff.comp h3ρ, hcs, hts.trans Set.inter_subset_left, ?_⟩
  set f : (Fin n → Fin n → Cinf E) → ℂ := fun a => (ρ a : ℂ) * onMatInf W (Matrix.of a) with hfdef
  have e : smoothMatInf (fun x => (ρ x : ℂ)) W 1 = ∫ a, f a := by
    simp [smoothMatInf, f]
  have hsub : tsupport f ⊆ S := tsupport_mul_subset_left.trans (hts.trans Set.inter_subset_left)
  have hfc : Continuous f :=
    ((Complex.continuous_ofReal.comp h3ρ.continuous).continuousOn.mul hF).continuous_of_tsupport_subset hS hsub
  have hfs : HasCompactSupport f := hcs.mul_right
  have hint : Integrable f volume := hfc.integrable_of_hasCompactSupport hfs
  have hnn : ∀ a, 0 ≤ (c * f a).re := by
    intro a
    have hr : 0 ≤ ρ a := (h4ρ ⟨a, rfl⟩).1
    have eq : (c * f a).re = ρ a * (c * onMatInf W (Matrix.of a)).re := by
      simp only [f]
      rw [mul_left_comm, Complex.re_ofReal_mul]
    rw [eq]
    by_cases ha : ρ a = 0
    · simp [ha]
    · have : a ∈ U := h1ρ (subset_tsupport _ ha)
      exact mul_nonneg hr (le_of_lt this.2)
  have hne : (c * f x0).re ≠ 0 := by
    simp only [f]
    rw [h5ρ, hval]
    simpa using hpos.ne'
  have hcont : Continuous fun a => (c * f a).re := Complex.continuous_re.comp (continuous_const.mul hfc)
  have hsupp : HasCompactSupport fun a => (c * f a).re :=
    hfs.comp_left (g := fun z : ℂ => (c * z).re) (by simp)
  have key : 0 < ∫ a, (c * f a).re ∂volume :=
    hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hsupp hnn (x := x0) hne
  have hre : ∫ a, (c * f a).re = (∫ a, c * f a).re := integral_re (hint.const_mul c)
  rw [e]
  intro h0
  rw [hre, integral_const_mul, h0, mul_zero, Complex.zero_re] at key
  exact lt_irrefl _ key

end GlobalTheory.JSW.MirCinf
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem functionFieldMap_bijective_of_isIso_restrict : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] (U : X.Opens), (U : Set X).Nonempty → IsIso (s ∣_ U) → Function.Bijective (functionFieldMap s) := by
  intro X Y _ _ s _ U hU hiso
  have hg : s (genericPoint Y) = genericPoint X := by
    have h := (genericPoint_spec Y).image s.continuous
    rw [Set.image_univ, s.denseRange.closure_range] at h
    exact h.eq (genericPoint_spec X)
  have hmem : genericPoint Y ∈ s ⁻¹ᵁ U := by
    change s (genericPoint Y) ∈ U
    rw [hg]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have h1 : IsIso ((s ∣_ U).stalkMap ⟨genericPoint Y, hmem⟩) :=
    ((isIso_iff_isIso_stalkMap (s ∣_ U)).1 hiso).2 _
  have h2 : IsIso (s.stalkMap (genericPoint Y)) :=
    ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (morphismRestrictStalkMap s U ⟨genericPoint Y, hmem⟩)).mp h1
  have h3 : ∀ (x y : X) (_ : x = y) (h : x ⤳ y), IsIso (X.presheaf.stalkSpecializes h) := by
    rintro x y rfl h
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    infer_instance
  unfold functionFieldMap
  have h4 := h3 _ _ hg (hg ▸ specializes_rfl)
  exact ConcreteCategory.bijective_of_isIso _

end GlobalTheory.Discrepancy
end
