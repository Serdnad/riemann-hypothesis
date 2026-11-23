module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Instances.Matrix
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle128
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle125
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle128
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle124
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle150
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle131
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.ContraSub

open GlobalTheory.ContraRefl

section General

variable {G V X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]

def incl {π : Representation ℂ G V} (S : Subrepresentation π) :
    S.toRepresentation.IntertwiningMap π where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := by ext _; rfl

theorem isSmooth_sub {π : Representation ℂ G V} (hπ : IsSmooth π) (S : Subrepresentation π) :
    IsSmooth S.toRepresentation := fun x => by
  have : {g : G | S.toRepresentation g x = x} = {g : G | π g x.1 = x.1} := by
    ext g; exact Subtype.ext_iff
  rw [this]; exact hπ x.1

theorem contraMap_incl_surjective
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {π : Representation ℂ G V} (hπ : IsSmooth π) (S : Subrepresentation π) :
    Function.Surjective (contraMap (incl S)) := by
  intro l
  obtain ⟨K, ho, hc, hKs⟩ := hG _ ((isSmooth_contra S.toRepresentation l).mem_nhds (by simp))
  have hlK : l ∈ fixed (contra S.toRepresentation) K := mem_fix.2 fun h hh => hKs hh
  obtain ⟨l₀, hl₀⟩ := LinearMap.exists_extend (l : Module.Dual ℂ S.toSubmodule)
  obtain ⟨l', h1, h2⟩ := exists_fixed_contra hπ ho hc (l₀ ∘ₗ (fixed π K).subtype)
  have hl'K : l' ∈ fixed (contra π) K := mem_fix.2 h1
  refine ⟨l', Subtype.ext (form_ext (isSmooth_sub hπ S) hc (fun h hh w => ?_) (fun h hh w => ?_)
    fun w hw => ?_)⟩
  · exact invariant_of_fixed ⟨l', hl'K⟩ h hh (w : V)
  · exact invariant_of_fixed ⟨l, hlK⟩ h hh w
  · have hwK : (w : V) ∈ fixed π K :=
      mem_fix.2 fun h hh => congrArg Subtype.val (mem_fix.1 hw h hh)
    have e1 := h2 ⟨w, hwK⟩
    have e2 := LinearMap.congr_fun hl₀ w
    exact e1.trans e2

theorem contraMap_injective {Y : Type} [AddCommGroup Y] [Module ℂ Y] {σ : Representation ℂ G X}
    {τ : Representation ℂ G Y} (f : σ.IntertwiningMap τ) (hf : Function.Surjective f) :
    Function.Injective (contraMap f) := by
  intro l l' h
  refine Subtype.ext (LinearMap.ext fun y => ?_)
  obtain ⟨x, rfl⟩ := hf y
  exact LinearMap.congr_fun (congrArg Subtype.val h) x

theorem isSubquotient_contra
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {σ : Representation ℂ G X} {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
    (h : IsSubquotient σ ρ) : IsSubquotient (contra σ) (contra ρ) := by
  obtain ⟨S, f, hf⟩ := h
  exact (IsSubquotient.of_injective (contraMap f) (contraMap_injective f hf)).trans
    (IsSubquotient.of_surjective (contraMap (incl S)) (contraMap_incl_surjective hG hρ S))

end General

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin N) k) V) (ρ : Representation ℂ (GL (Fin N) k) W),
    IsSmooth σ → IsSmooth ρ → IsSubquotient σ ρ → IsSubquotient (contra σ) (contra ρ) := by
  intro k _ _ _ _ N V W _ _ _ _ σ ρ _ hρ h
  refine isSubquotient_contra (fun U hU => ?_) hρ h
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k (Fin N) U hU
  exact ⟨J, h1, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

end GlobalTheory.CompanionTheory.ContraSub
end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

section Abstract

variable {G : Type} [Group G]

def dcos (Q P : Subgroup G) (x : G) : Set G := {g | ∃ q ∈ Q, ∃ p ∈ P, g = q * x * p}

def LocSec [TopologicalSpace G] (Q P : Subgroup G) (x : G) : Prop :=
  ∀ OQ ∈ 𝓝 (1 : G), ∀ OP ∈ 𝓝 (1 : G), ∃ O ∈ 𝓝 (1 : G), ∀ u ∈ O, x * u ∈ dcos Q P x →
    ∃ s ∈ Q, s ∈ OQ ∧ ∃ p ∈ P, p ∈ OP ∧ x * u = s * x * p

variable [TopologicalSpace G] [IsTopologicalGroup G]
  {W₁ W₂ : Type} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]

def resInd {Q P : Subgroup G} {x : G} (σ : Representation ℂ Q W₁) (H : Subgroup P)
    (hH : ∀ p : P, p ∈ H ↔ x * (p : G) * x⁻¹ ∈ Q) (τ : Representation ℂ H W₂) (E : W₁ ≃ₗ[ℂ] W₂)
    (hE : ∀ (h : H) (hq : x * ((h : P) : G) * x⁻¹ ∈ Q) (v : W₁), τ h (E v) = E (σ ⟨_, hq⟩ v)) :
    smoothPart (ind Q σ) →ₗ[ℂ] smoothPart (ind H τ) where
  toFun f := ⟨⟨fun p => E (f.1.1 (x * (p : G))), by
      intro h p
      have hq := (hH h).1 h.2
      have e : x * (((h * p : P)) : G) = (⟨_, hq⟩ : Q) * (x * (p : G)) := by
        simp [mul_assoc]
      show E (f.1.1 (x * (((h : P) * p : P) : G))) = τ h (E (f.1.1 (x * (p : G))))
      rw [hE h hq, show x * (((h : P) * p : P) : G) = ((⟨_, hq⟩ : Q) : G) * (x * (p : G)) from e]
      exact congrArg E (f.1.2 _ _)⟩, by
      have hf : IsOpen {g : G | ind Q σ g f.1 = f.1} := f.2
      have hopen : IsOpen {p : P | ind Q σ (p : G) f.1 = f.1} := hf.preimage continuous_subtype_val
      refine mem_smoothPart_of_nhds ?_
      filter_upwards [hopen.mem_nhds (by simp)] with p hp
      refine Subtype.ext (funext fun y => ?_)
      have := congrArg (fun F : indSpace Q σ => F.1 (x * (y : G))) hp
      show E (f.1.1 (x * ((y * p : P) : G))) = E (f.1.1 (x * (y : G)))
      rw [show x * ((y * p : P) : G) = x * (y : G) * (p : G) by simp [mul_assoc]]
      exact congrArg E this⟩
  map_add' a b := by
    refine Subtype.ext (Subtype.ext (funext fun p => ?_))
    exact map_add E _ _
  map_smul' c a := by
    refine Subtype.ext (Subtype.ext (funext fun p => ?_))
    exact map_smul E _ _

end Abstract

section Concrete

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def eGPg {m j n : ℕ} (h : m + j = n) : (Σ x, Two (Fin m) (Fin (j + 1)) x) ≃ Fin (n + 1) :=
  two (stdSum (by omega))

def HGPg {m j n : ℕ} (h : m + j = n) : Subgroup (Mir k n) := (parab k (eGPg h)).comap (Mir k n).subtype

def hgpInclg {m j n : ℕ} (h : m + j = n) : HGPg k h →* parab k (eGPg h) where
  toFun g := ⟨((g : Mir k n) : GL (Fin (n + 1)) k), g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem hgpg_block_mem {m j n : ℕ} (h : m + j = n) (g : HGPg k h) :
    (leviProj k (eGPg h) (hgpInclg k h g) true : GL (Fin (j + 1)) k) ∈ Mir k j := by
  subst h
  exact hgp_block_mem _ _ g

def gpProjg {m j n : ℕ} (h : m + j = n) : HGPg k h →* GL (Fin m) k × Mir k j :=
  MonoidHom.prod ((Pi.evalMonoidHom (fun x => GL (Two (Fin m) (Fin (j + 1)) x) k) false).comp
      ((leviProj k (eGPg h)).comp (hgpInclg k h)))
    (((Pi.evalMonoidHom (fun x => GL (Two (Fin m) (Fin (j + 1)) x) k) true).comp
      ((leviProj k (eGPg h)).comp (hgpInclg k h))).codRestrict (Mir k j) (hgpg_block_mem k h))

def wPerm {i t : ℕ} (h : (i + 1) + t = i + t + 1) : Equiv.Perm (Fin (i + t + 1)) :=
  (two (stdSum h)).symm.trans (ePG i t)

def wGL {i t : ℕ} (h : (i + 1) + t = i + t + 1) : GL (Fin (i + t + 1)) k where
  val := (1 : Matrix _ _ k).submatrix (wPerm h) id
  inv := (1 : Matrix _ _ k).submatrix id (wPerm h)
  val_inv := by
    rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, mul_one]
    exact Matrix.submatrix_one_equiv (wPerm h)
  inv_val := by
    rw [← Matrix.submatrix_mul _ _ _ (wPerm h) _ (wPerm h).bijective, mul_one]
    exact Matrix.submatrix_one_equiv (Equiv.refl _)

end Concrete

section Inducing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

abbrev sQ {r t N : ℕ} (h : r + t = N) (π₁ : Representation ℂ (GL (Fin r) k) V)
    (π₂ : Representation ℂ (GL (Fin t) k) W) :
    Representation ℂ (parab k (two (stdSum h))) (⨂[ℂ] x, TwoT V W x) :=
  (twist (piTensor (twoRep π₁ π₂)) (deltaHalf k (Two (Fin r) (Fin t)))).comp (leviProj k (two (stdSum h)))

abbrev tE (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] :
    (⨂[ℂ] x, TwoT V W x) ≃ₗ[ℂ] V ⊗[ℂ] W :=
  Exponents.boolTensorEquiv (X := TwoT V W)

end Inducing

section Row

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_updateRow_one {N : ℕ} (a : Fin N) (y : Fin N → k) :
    ((1 : Matrix (Fin N) (Fin N) k).updateRow a y).det = y a := by
  have h := Matrix.cramer_apply (1 : Matrix (Fin N) (Fin N) k) y a
  rw [Matrix.cramer_one] at h
  have e : ((1 : Matrix (Fin N) (Fin N) k).updateCol a y) = ((1 : Matrix (Fin N) (Fin N) k).updateRow a y)ᵀ := by
    rw [← Matrix.updateCol_transpose, Matrix.transpose_one]
  rw [e, Matrix.det_transpose] at h
  simpa using h.symm

theorem exists_rowSec {N : ℕ} (a : Fin N) : ∃ b : (Fin N → k) → GL (Fin N) k,
    ContinuousAt b (Pi.single a 1) ∧ b (Pi.single a 1) = 1 ∧
      ∀ y : Fin N → k, y a ≠ 0 → (b y : Matrix (Fin N) (Fin N) k) = (1 : Matrix (Fin N) (Fin N) k).updateRow a y := by
  classical
  let M : (Fin N → k) → Matrix (Fin N) (Fin N) k := fun y => (1 : Matrix (Fin N) (Fin N) k).updateRow a y
  have hM : Continuous M := by
    refine continuous_matrix fun c d => ?_
    by_cases h : c = a
    · subst h
      simpa [M] using continuous_apply d
    · simpa [M, Matrix.updateRow_ne h] using continuous_const
  have hdet : ∀ y, (M y).det = y a := fun y => det_updateRow_one a y
  let b : (Fin N → k) → GL (Fin N) k := fun y =>
    if h : y a ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (M y) (by rw [hdet]; exact h) else 1
  have hb : ∀ y : Fin N → k, y a ≠ 0 → (b y : Matrix (Fin N) (Fin N) k) = M y := fun y h => by
    simp only [b, dif_pos h]
    rfl
  have h0 : (Pi.single a 1 : Fin N → k) a ≠ 0 := by simp
  have hne : ∀ᶠ y : Fin N → k in 𝓝 (Pi.single a 1), y a ≠ 0 :=
    (continuous_apply a).continuousAt.eventually_ne h0
  refine ⟨b, ?_, ?_, hb⟩
  · rw [Units.isInducing_embedProduct.continuousAt_iff]
    have h1 : ContinuousAt (fun y => (b y : Matrix (Fin N) (Fin N) k)) (Pi.single a 1) :=
      hM.continuousAt.congr (hne.mono fun y h => (hb y h).symm)
    have h2 : ContinuousAt (fun y => (((b y)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)) (Pi.single a 1) := by
      have h3 : ContinuousAt (fun y : Fin N → k => (y a)⁻¹ • (M y).adjugate) (Pi.single a 1) :=
        ((continuous_apply a).continuousAt.inv₀ h0).smul hM.matrix_adjugate.continuousAt
      refine h3.congr (hne.mono fun y h => ?_)
      show (y a)⁻¹ • (M y).adjugate = (((b y)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
      rw [Matrix.coe_units_inv, hb y h, Matrix.inv_def, hdet, Ring.inverse_eq_inv]
    exact h1.prodMk (MulOpposite.continuous_op.continuousAt.comp h2)
  · ext1
    rw [hb _ h0]
    show (1 : Matrix (Fin N) (Fin N) k).updateRow a (Pi.single a 1) = 1
    ext c d
    by_cases h : c = a
    · subst h
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    · simp [Matrix.updateRow_ne h]

end Row

end GlobalTheory.CompanionTheory.BZRes

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi ValuativeRel
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.MirLevi.Bump

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E]

def IntM (m : GL (Fin n) k) : Prop :=
  ∀ i, Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k) i) ∈ polyBall (k := k) n 1

theorem intM_one : IntM (1 : GL (Fin n) k) := by
  intro i j
  show valuation k (((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k ((1 : kˣ) : k)
  by_cases h : i = j
  · simp [h]
  · simp [one_apply, h]

theorem IntM.mulVec_mem {m : GL (Fin n) k} (hm : IntM m) {s : kˣ} {v : Fin n → k}
    (hv : Multiplicative.ofAdd v ∈ polyBall (k := k) n s) :
    Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k).mulVec v) ∈ polyBall (k := k) n s :=
  fun i => dotProduct_mem_cball (a := 1) (b := s) (c := s) (by simp) (hm i) hv

theorem isOpen_intM : IsOpen {m : GL (Fin n) k | IntM m} := by
  have h : {m : GL (Fin n) k | IntM m} = ⋂ i, (fun m : GL (Fin n) k =>
      Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k) i)) ⁻¹'
        (polyBall (k := k) n 1 : Set (Multiplicative (Fin n → k))) := by
    ext m
    simp [IntM]
  rw [h]
  refine isOpen_iInter_of_finite fun i => (isOpen_polyBall n 1).preimage ?_
  exact continuous_ofAdd.comp (continuous_pi fun j => Units.continuous_val.matrix_elem i j)

theorem continuous_colv : Continuous (colv : Mir k n → Fin n → k) :=
  continuous_pi fun i => (Units.continuous_val.comp continuous_subtype_val).matrix_elem (Fin.castSucc i) (Fin.last n)

theorem continuous_mvec : Continuous (mvec : Mir k n → Fin n → k) := by
  have h1 : Continuous fun x : Mir k n =>
      (((mirabolicProjection k n x)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) :=
    Units.continuous_val.comp (continuous_inv.comp (GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k n))
  exact h1.matrix_mulVec continuous_colv

theorem continuous_lv : Continuous (lv k n) :=
  continuous_induced_rng.2 (GlobalTheory.CompanionTheory.BZMirFun.continuous_levi k n)

def bumpF (ρ : Representation ℂ (LH k n) E) (s : kˣ) (e : E) (g : Mir k n) : E :=
  @ite _ (Multiplicative.ofAdd (mvec g) ∈ polyBall (k := k) n s) (Classical.propDecidable _)
    (ρ (lv k n (mirabolicProjection k n g)) e) 0

variable (ρ : Representation ℂ (LH k n) E) (s : kˣ) (e : E)

theorem bumpF_levi_mul (m : GL (Fin n) k) (g : Mir k n) :
    bumpF ρ s e (levi k n m * g) = ρ (lv k n m) (bumpF ρ s e g) := by
  unfold bumpF
  rw [mvec_levi_mul, map_mul, mirProj_levi, map_mul, map_mul, Module.End.mul_apply]
  split_ifs <;> simp

theorem bumpF_equi (h : LH k n) (g : Mir k n) :
    bumpF ρ s e ((h : Mir k n) * g) = ρ h (bumpF ρ s e g) := by
  obtain ⟨m, hm⟩ := h.2
  have e1 : h = lv k n m := Subtype.ext hm.symm
  rw [e1]
  exact bumpF_levi_mul ρ s e m g

theorem bumpF_levi_uv (q : GL (Fin n) k) (w : Fin n → k) :
    bumpF ρ s e (levi k n q * uv n w) =
      @ite _ (Multiplicative.ofAdd w ∈ polyBall (k := k) n s) (Classical.propDecidable _)
        (ρ (lv k n q) e) 0 := by
  unfold bumpF
  rw [mvec_levi_mul_uv, map_mul, mirProj_levi, mirProj_uv, mul_one]

theorem bumpF_uv (w : Fin n → k) :
    bumpF ρ s e (uv n w) =
      @ite _ (Multiplicative.ofAdd w ∈ polyBall (k := k) n s) (Classical.propDecidable _) e 0 := by
  have h := bumpF_levi_uv ρ s e 1 w
  rw [map_one (levi k n), one_mul, map_one (lv k n), map_one ρ] at h
  simpa using h

theorem mul_formula (p m : GL (Fin n) k) (v a : Fin n → k) :
    (levi k n p * uv n v) * (levi k n m * uv n a) = levi k n (p * m) *
      uv n (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v + a) := by
  rw [uv_add, map_mul, mul_assoc (levi k n p), ← mul_assoc (uv n v), uv_mul_levi]
  simp only [mul_assoc]

theorem bumpF_fix (p m : GL (Fin n) k) (v a : Fin n → k) (h1 : IntM m) (h2 : IntM m⁻¹)
    (hm : ρ (lv k n m) e = e) (ha : Multiplicative.ofAdd a ∈ polyBall (k := k) n s) :
    bumpF ρ s e ((levi k n p * uv n v) * (levi k n m * uv n a)) = bumpF ρ s e (levi k n p * uv n v) := by
  rw [mul_formula, bumpF_levi_uv, bumpF_levi_uv, map_mul, map_mul, Module.End.mul_apply, hm]
  have hiff : Multiplicative.ofAdd (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v + a) ∈
      polyBall (k := k) n s ↔ Multiplicative.ofAdd v ∈ polyBall (k := k) n s := by
    constructor
    · intro h
      have h3 : Multiplicative.ofAdd (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v) ∈
          polyBall (k := k) n s := by
        have h4 := mul_mem h (inv_mem ha)
        rwa [ofAdd_add, mul_inv_cancel_right] at h4
      have h5 := h1.mulVec_mem h3
      rwa [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at h5
    · intro h
      rw [ofAdd_add]
      exact mul_mem (h2.mulVec_mem h) ha
  by_cases hv : Multiplicative.ofAdd v ∈ polyBall (k := k) n s
  · rw [if_pos hv, if_pos (hiff.2 hv)]
  · rw [if_neg hv, if_neg (fun c => hv (hiff.1 c))]

def nbhd : Set (Mir k n) :=
  {x | IntM (mirabolicProjection k n x) ∧ IntM (mirabolicProjection k n x)⁻¹ ∧ ρ (lv k n (mirabolicProjection k n x)) e = e ∧
    Multiplicative.ofAdd (mvec x) ∈ polyBall (k := k) n s}

theorem isOpen_nbhd (hρ : IsSmooth ρ) : IsOpen (nbhd ρ s e) := by
  unfold nbhd
  have hp := GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k n
  exact (isOpen_intM.preimage hp).inter ((isOpen_intM.preimage (continuous_inv.comp hp)).inter
    (((hρ e).preimage (continuous_lv.comp hp)).inter
      ((isOpen_polyBall n s).preimage (continuous_ofAdd.comp continuous_mvec))))

theorem one_mem_nbhd : (1 : Mir k n) ∈ nbhd ρ s e := by
  have hm : mvec (1 : Mir k n) = 0 := by
    have h := mvec_uv (k := k) n 0
    rwa [uv_zero] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [map_one]; exact intM_one
  · rw [map_one, inv_one]; exact intM_one
  · simp
  · rw [hm]; exact one_mem _

theorem bumpF_mul_nbhd (g x : Mir k n) (hx : x ∈ nbhd ρ s e) :
    bumpF ρ s e (g * x) = bumpF ρ s e g := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have h := bumpF_fix ρ s e (mirabolicProjection k n g) (mirabolicProjection k n x) (mvec g) (mvec x) h1 h2 h3 h4
  rwa [← decomp g, ← decomp x] at h

theorem bumpF_mem : bumpF ρ s e ∈ indSpace (LH k n) ρ := fun h g => bumpF_equi ρ s e h g

theorem bumpF_smooth (hρ : IsSmooth ρ) :
    (⟨bumpF ρ s e, bumpF_mem ρ s e⟩ : indSpace (LH k n) ρ) ∈ smoothPart (ind (LH k n) ρ) := by
  have hfix : nbhd ρ s e ⊆ (GlobalTheory.CompanionTheory.LeibPhi.stabSub (ind (LH k n) ρ)
      (⟨bumpF ρ s e, bumpF_mem ρ s e⟩ : indSpace (LH k n) ρ) : Set (Mir k n)) := by
    intro x hx
    apply Subtype.ext
    funext g
    exact bumpF_mul_nbhd ρ s e g x hx
  exact (GlobalTheory.CompanionTheory.LeibPhi.stabSub (ind (LH k n) ρ)
    (⟨bumpF ρ s e, bumpF_mem ρ s e⟩ : indSpace (LH k n) ρ)).isOpen_of_mem_nhds (g := 1)
    (Filter.mem_of_superset ((isOpen_nbhd ρ s e hρ).mem_nhds (one_mem_nbhd ρ s e)) hfix)

theorem bumpF_support : ∃ C : Set (Mir k n), IsCompact C ∧ ∀ g, bumpF ρ s e g ≠ 0 →
    ∃ h ∈ LH k n, ∃ c ∈ C, g = h * c := by
  refine ⟨unipIn k n '' (polyBall (k := k) n s : Set (Multiplicative (Fin n → k))),
    (isCompact_polyBall n s).image (continuous_unipIn n), fun g hg => ?_⟩
  have hL : Multiplicative.ofAdd (mvec g) ∈ polyBall (k := k) n s := by
    by_contra hc
    exact hg (if_neg hc)
  exact ⟨levi k n (mirabolicProjection k n g), ⟨_, rfl⟩, uv n (mvec g), ⟨_, hL, rfl⟩, decomp g⟩

theorem exists_bump_restr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (LH k n) E), IsSmooth ρ → ∀ (s : kˣ) (e : E),
    ∃ b : cIndSpace (LH k n) ρ, ∀ v : Fin n → k, restr ρ b v =
      @ite _ (Multiplicative.ofAdd v ∈ polyBall (k := k) n s) (Classical.propDecidable _) e 0 := by
  intro k _ _ _ _ n E _ _ ρ hρ s e
  exact ⟨⟨⟨⟨bumpF ρ s e, bumpF_mem ρ s e⟩, bumpF_smooth ρ s e hρ⟩, bumpF_support ρ s e⟩,
    fun v => bumpF_uv ρ s e v⟩

end GlobalTheory.CompanionTheory.MirLevi.Bump

end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.kuenneth_mayer_vietoris_right : MVBij → CovDesc → ∀ {K : Type} [Field K] (E : XD K) (U₂ : ObjectProperty E.C₂) {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty E.C₁) (W : ι → ObjectProperty E.D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₁.obj T)) (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → U₂ (E.L₂.obj T)), (∀ S : Finset ι, S.Nonempty → E.Kun (capU V S) U₂ (capU W S) (h₁ S) (h₂ S)) → E.Kun (capU V ∅) U₂ (capU W ∅) (h₁ ∅) (h₂ ∅) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.glue_l | exact GlobalTheory.CompanionTheory.KunGlue.glue_l | (intros; apply GlobalTheory.CompanionTheory.KunGlue.glue_l <;> assumption)
end
