module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle003
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle188
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle190
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

noncomputable section

open Formalism.IndefR.Links
open scoped InnerProductSpace

namespace GlobalTheory.HilbertModel

def Syn {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) : Type := V

instance {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) : AddCommGroup (Syn V) :=
  inferInstanceAs (AddCommGroup V)

instance {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) : Module ℂ (Syn V) :=
  inferInstanceAs (Module ℂ V)

def Syn.incl {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) : Syn V →ₗ[ℂ] X := V.subtype

theorem Syn.incl_mem {X : Type} [AddCommGroup X] [Module ℂ X] {V : Submodule ℂ X} (x : Syn V) : Syn.incl V x ∈ V :=
  (show V from x).2

theorem Syn.incl_injective {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) :
    Function.Injective (Syn.incl V) := Subtype.val_injective

theorem Syn.range_incl {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) :
    LinearMap.range (Syn.incl V) = V := V.range_subtype

@[reducible] def core {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) (ip : X → X → ℂ)
    (h : ∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, ∀ c : ℂ, ip x (y + c • z) = ip x y + c * ip x z ∧ ip y x = star (ip x y))
    (hp : ∀ x ∈ V, x ≠ 0 → 0 < (ip x x).re) : InnerProductSpace.Core ℂ (Syn V) :=
  have hs : ∀ x ∈ V, ∀ y ∈ V, ip y x = star (ip x y) := fun x hx y hy => (h x hx y hy 0 V.zero_mem 0).2
  have h0 : ∀ x ∈ V, ip x 0 = 0 := fun x hx => by
    have := (h x hx 0 V.zero_mem 0 V.zero_mem 1).1
    simpa using this
  { inner := fun x y => ip (Syn.incl V x) (Syn.incl V y)
    conj_inner_symm := fun x y => (hs _ (Syn.incl_mem y) _ (Syn.incl_mem x)).symm
    re_inner_nonneg := fun x => by
      show 0 ≤ (ip (Syn.incl V x) (Syn.incl V x)).re
      by_cases hx : Syn.incl V x = 0
      · rw [hx, h0 0 V.zero_mem]; simp
      · exact (hp _ (Syn.incl_mem x) hx).le
    add_left := fun x y z => by
      show ip (Syn.incl V (x + y)) (Syn.incl V z) = ip (Syn.incl V x) (Syn.incl V z) + ip (Syn.incl V y) (Syn.incl V z)
      have h1 := (h _ (Syn.incl_mem z) _ (Syn.incl_mem x) _ (Syn.incl_mem y) 1).1
      rw [one_smul, one_mul] at h1
      rw [hs _ (Syn.incl_mem z) _ (Syn.incl_mem (x + y)), map_add (f := _), h1, star_add,
        ← hs _ (Syn.incl_mem z) _ (Syn.incl_mem x), ← hs _ (Syn.incl_mem z) _ (Syn.incl_mem y)]
    smul_left := fun x y r => by
      show ip (Syn.incl V (r • x)) (Syn.incl V y) = starRingEnd ℂ r * ip (Syn.incl V x) (Syn.incl V y)
      have h1 := (h _ (Syn.incl_mem y) _ V.zero_mem _ (Syn.incl_mem x) r).1
      rw [zero_add, h0 _ (Syn.incl_mem y), zero_add] at h1
      rw [hs _ (Syn.incl_mem y) _ (Syn.incl_mem (r • x)), map_smul, h1, star_mul',
        ← hs _ (Syn.incl_mem y) _ (Syn.incl_mem x)]
      rfl
    definite := fun x hx => by
      have hx' : ip (Syn.incl V x) (Syn.incl V x) = 0 := hx
      by_contra hne
      have h1 : Syn.incl V x ≠ 0 := fun h2 => hne (Syn.incl_injective V (by rw [h2, map_zero]))
      have := hp _ (Syn.incl_mem x) h1
      rw [hx'] at this
      simp at this }

theorem exists_hmod : ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) (ip : X → X → ℂ), FiniteDimensional ℂ V → (∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, ∀ c : ℂ, ip x (y + c • z) = ip x y + c * ip x z ∧ ip y x = star (ip x y)) → (∀ x ∈ V, x ≠ 0 → 0 < (ip x x).re) → ∃ M : HMod X, M.Is V ip := by
  intro X _ _ V ip hf h hp
  let cd : InnerProductSpace.Core ℂ (Syn V) := core V ip h hp
  let nH : NormedAddCommGroup (Syn V) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (cd := cd)
  let iH : InnerProductSpace ℂ (Syn V) := InnerProductSpace.ofCore cd.toCore
  exact ⟨@Formalism.IndefR.Links.HMod.mk X _ _ (Syn V) nH iH hf (Syn.incl V), Syn.incl_injective V, Syn.range_incl V, fun _ _ => rfl⟩

section Lift

variable {X : Type} [AddCommGroup X] [Module ℂ X] {M : HMod X} {V : Submodule ℂ X} {ip : X → X → ℂ}

def equivSub (hM : M.Is V ip) : M.H ≃ₗ[ℂ] V :=
  (LinearEquiv.ofInjective M.e hM.1).trans (LinearEquiv.ofEq _ _ hM.2.1)

@[simp] theorem coe_equivSub (hM : M.Is V ip) (x : M.H) : (equivSub hM x : X) = M.e x := rfl

@[simp] theorem e_equivSub_symm (hM : M.Is V ip) (v : V) : M.e ((equivSub hM).symm v) = v := by
  rw [← coe_equivSub hM, LinearEquiv.apply_symm_apply]

theorem exists_lift_fun {R A : Type*} [Semiring R] [AddCommMonoid A] [Module R A] (σ : R →+* ℂ) (hM : M.Is V ip)
    (f : A → X) (hadd : ∀ a b, f (a + b) = f a + f b) (hsmul : ∀ (c : R) a, f (c • a) = σ c • f a) (hf : ∀ a, f a ∈ V) :
    ∃ g : A →ₛₗ[σ] M.H, ∀ a, M.e (g a) = f a :=
  ⟨{ toFun := fun a => (equivSub hM).symm ⟨f a, hf a⟩
     map_add' := fun a b => hM.1 (by simp [hadd])
     map_smul' := fun c a => hM.1 (by simp [hsmul]) }, fun a => e_equivSub_symm hM _⟩

theorem exists_lift {R A : Type*} [Semiring R] [AddCommMonoid A] [Module R A] {σ : R →+* ℂ} (hM : M.Is V ip)
    (f : A →ₛₗ[σ] X) (hf : ∀ a, f a ∈ V) : ∃ g : A →ₛₗ[σ] M.H, ∀ a, M.e (g a) = f a :=
  exists_lift_fun σ hM f f.map_add f.map_smulₛₗ hf

variable {X' : Type} [AddCommGroup X'] [Module ℂ X'] {M' : HMod X'} {V' : Submodule ℂ X'} {ip' : X' → X' → ℂ}

end Lift

end GlobalTheory.HilbertModel
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.L2 Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OtherPlaces

theorem conj_mem_of_comap_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {w w' : HeightOneSpectrum (𝓞 E)}
    (h : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) =
      w'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))) (hne : w ≠ w') :
    ∀ c ∈ w.asIdeal, IsCMField.ringOfIntegersComplexConj E c ∈ w'.asIdeal := by
  have hsub : (w.asIdeal : Set (𝓞 E)) ⊆ w'.asIdeal ∪
      (w'.asIdeal.comap (IsCMField.ringOfIntegersComplexConj E).toRingEquiv.toRingHom : Ideal (𝓞 E)) := by
    intro y hy
    obtain ⟨x, hx⟩ := (IsCMField.RingOfIntegers.complexConj_eq_self_iff E
      (y * IsCMField.ringOfIntegersComplexConj E y)).1 (by simp [mul_comm])
    have hx' : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) x = y * IsCMField.ringOfIntegersComplexConj E y :=
      RingOfIntegers.ext hx
    have h1 : x ∈ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) := by
      rw [Ideal.mem_comap, hx']; exact Ideal.mul_mem_right _ _ hy
    rw [h, Ideal.mem_comap, hx'] at h1
    exact w'.isPrime.mem_or_mem h1
  rcases Ideal.subset_union.1 hsub with h1 | h1
  · exact absurd (HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top h1)) hne
  · exact fun c hc => h1 hc

theorem over_ne : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) →
    ∀ (t : T) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), s.v ∉ gPl D → s.w ∈ L.Q t →
      (∀ PP ∈ L.Pg, ∃ v', NG.OverPl PP v' ∧ v' ≠ s.v) ∧ (∀ PP ∈ L.Q t, PP ≠ s.w → ∃ v', NG.OverPl PP v' ∧ v' ≠ s.v) := by
  intro D T L μ0 hL hPg t s hs hsQ
  refine ⟨fun PP hPP => ⟨PP.under (𝓞 (maximalRealSubfield D.host.E)), rfl, fun e => hs ?_⟩,
    fun PP hPP hne => ⟨PP.under (𝓞 (maximalRealSubfield D.host.E)), rfl, fun e => ?_⟩⟩
  · obtain ⟨k, v, rfl⟩ := (hPg PP).1 hPP
    exact ⟨D.naut.plGw k v, congrArg HeightOneSpectrum.asIdeal e, k, D.naut.plGw_over k v⟩
  · letI := D.host.isCMField_hostE
    refine (hL.Q_pl t s.w hsQ).2 PP hPP fun c hc => ⟨_, conj_mem_of_comap_eq
      (s.w_under.trans (congrArg HeightOneSpectrum.asIdeal e).symm) hne.symm c hc, rfl⟩

end GlobalTheory.OtherPlaces
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct

namespace GlobalTheory.OrientedSmall

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {R : Type} [CommRing R] (c : R →+* R) {n m : ℕ}

theorem sum_eq_trace_oriented (P : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R)
    (x y : Matrix (Fin m) (Fin n) R) :
    ∑ a, ∑ b, ∑ e, ∑ d, P a b * c (y e b) * K e d * x d a = (P * (y.map c)ᵀ * K * x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ∑ b, ∑ e, ∑ d, P a b * c (y e b) * K e d * x d a
      = ∑ e, ∑ b, ∑ d, P a b * c (y e b) * K e d * x d a := Finset.sum_comm
    _ = ∑ e, ∑ d, ∑ b, P a b * c (y e b) * K e d * x d a := Finset.sum_congr rfl fun e _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem trace_coord (J P : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R)
    (hPJ : P * J = 1) (hP : P.map c = Pᵀ) (x y : Matrix (Fin m) (Fin n) R) :
    (P * (y.map c)ᵀ * K * x).trace = ((((y * P)ᵀ).map c)ᵀ * Jᵀ * (x * P)ᵀ * Kᵀ).trace := by
  have e1 : Jᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hPJ, Matrix.transpose_one]
  rw [Matrix.transpose_map, Matrix.transpose_transpose, Matrix.map_mul, hP, Matrix.transpose_mul]
  calc (P * (y.map c)ᵀ * K * x).trace
      = (P * (y.map c)ᵀ * (K * x)).trace := by simp only [Matrix.mul_assoc]
    _ = (K * x * (P * (y.map c)ᵀ)).trace := Matrix.trace_mul_comm _ _
    _ = (K * x * (P * (y.map c)ᵀ))ᵀ.trace := (Matrix.trace_transpose _).symm
    _ = (y.map c * Pᵀ * xᵀ * Kᵀ).trace := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = (y.map c * Pᵀ * (Jᵀ * Pᵀ) * xᵀ * Kᵀ).trace := by rw [e1, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem act_coord (J P g g' : Matrix (Fin n) (Fin n) R) (h : Matrix (Fin m) (Fin m) R)
    (hPJ : P * J = 1) (hg : (g.map c)ᵀ * J * g = J) (hgg : g * g' = 1) (x : Matrix (Fin m) (Fin n) R) :
    (h * x * g' * P)ᵀ = g.map c * (x * P)ᵀ * hᵀ := by
  have hJP : J * P = 1 := mul_eq_one_comm.1 hPJ
  have key : g' * P = P * (g.map c)ᵀ := by
    calc g' * P = (P * J) * g' * P := by rw [hPJ, Matrix.one_mul]
      _ = P * ((g.map c)ᵀ * J * g) * g' * P := by rw [hg]
      _ = P * (g.map c)ᵀ * (J * ((g * g') * P)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hgg, Matrix.one_mul, hJP, Matrix.mul_one]
  rw [Matrix.mul_assoc (h * x), key]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

end Generic

variable {D : D7}

theorem cA_incA (a : D.host.E) : cA D (incA D a) = incA D (star a) := by
  simp [cA, sigR, incA, inclR, CMData.sig, starRingEnd_apply]

theorem gram_conjTranspose (V : HSp D) : V.gramᴴ = V.gram := by
  refine Matrix.ext fun i j => ?_
  exact V.herm.eq (V.frame j) (V.frame i)

theorem gramInv_mul (V : HSp D) : (V.gram⁻¹).map (incA D) * V.gram.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem gramInv_map (V : HSp D) :
    ((V.gram⁻¹).map (incA D)).map (cA D) = ((V.gram⁻¹).map (incA D))ᵀ := by
  have h : (V.gram⁻¹)ᴴ = V.gram⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, gram_conjTranspose]
  ext i j
  have := congrFun (congrFun h j) i
  rw [Matrix.conjTranspose_apply] at this
  simp only [Matrix.map_apply, Matrix.transpose_apply]
  rw [cA_incA, this]

theorem mt_mul_inv (V : HSp D) (g : GA D V) :
    Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem hO_eq (S T : HSp D) (hr : S.rank ≤ T.rank) (x y : WO S T) :
    hO S T x y = hHom S T (toTWsmall S T y) (toTWsmall S T x) := by
  unfold hO hHom
  rw [if_pos hr]
  have s := sum_eq_trace (cA D) (S.gram.map (incA D)) (T.gram.map (incA D))
    (toTWsmall S T y) (toTWsmall S T x)
  have s' := sum_eq_trace_oriented (cA D) ((S.gram⁻¹).map (incA D)) (T.gram.map (incA D)) x y
  simp only [Matrix.map_apply] at s s'
  rw [s, s']
  exact trace_coord (cA D) _ _ _ (gramInv_mul S) (gramInv_map S) x y

theorem bridgeSmall (D : D7) : BridgeSmall D := by
  intro S T hr
  refine ⟨fun x y => ?_, fun g h x => ?_⟩
  · unfold symplO sympl
    rw [hO_eq S T hr]
  · unfold actHom
    rw [if_pos hr]
    exact act_coord (cA D) _ _ _ _ _ (gramInv_mul S) (mt_rel S g) (mt_mul_inv S g) x

end GlobalTheory.OrientedSmall

end
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_nhds_one_unitaryGroup_rationalPoint_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), ∃ U ∈ nhds (1 : HA (AF F) σ J), ∀ g ∈ U, (∃ γ : HFinIn (AF F) σ J, γ • (1 : HA (AF F) σ J) = g) → g = 1 := by
  first | exact @GlobalTheory.Mem.Vol.exists_nhds_one_rational_eq_one | exact GlobalTheory.Mem.Vol.exists_nhds_one_rational_eq_one | (intros; apply GlobalTheory.Mem.Vol.exists_nhds_one_rational_eq_one <;> assumption)
end

section


theorem _root_.GlobalTheory.T.weyl_lattice_duality : WeylLatticeDuality.Stmt := by
  first | exact @GlobalTheory.WeylLatDualProof.mainProof | exact GlobalTheory.WeylLatDualProof.mainProof | (intros; apply GlobalTheory.WeylLatDualProof.mainProof <;> assumption)
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.eq_zero_of_affineHyperplane_line_sums : ∀ (k W M : Type) [Field k] [Fintype k] [DecidableEq k] [AddCommGroup W] [Module k W] [Finite W] [AddCommGroup M] [Module ℂ M] (ψ : W → M), ψ 0 = 0 → (∀ g : Module.Dual k W, g ≠ 0 → ∑ᶠ x ∈ {x | g x = 1}, ψ x = 0) → (∀ x, ∑ a : kˣ, ψ ((a : k) • x) = 0) → ∀ x, ψ x = 0 := by
  first | exact @GlobalTheory.FiniteRadon.eq_zero_of_hyperplane_sums | exact GlobalTheory.FiniteRadon.eq_zero_of_hyperplane_sums | (intros; apply GlobalTheory.FiniteRadon.eq_zero_of_hyperplane_sums <;> assumption)
end
