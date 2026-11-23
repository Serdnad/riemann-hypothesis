module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle198
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle184
public import Formalism.FormalDegreeBessel.StatementG
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle199
import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParIffStepGap
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

namespace GlobalTheory.SphTheta

theorem isBorelU_inv_mixeq {L : Type} [Field L] {σ : L →+* L} {n : ℕ} {g : GU σ n} (hg : IsBorelU g) :
    IsBorelU g⁻¹ := by
  intro i j hij
  exact Formalism.UG.P.spherical_upper_inv (g : GL (Fin n) L) ((Formalism.UG.P.spherical_upper_iff _).1 hg) hij

theorem mixLat_form_borel : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) → (∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ v, ℓ' v = ℓ' s * ℓ v) → ∀ (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h → (∀ v, ℓ (ω (g, h) v) = ℓ (ω (g, h) s) * ℓ v) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (v : M), ℓ (ρ (embLow n' n z) (ω (g, h) v)) = ℓ (ω (g, h) s) * ℓ (ρ (embLow n' n (lowBlock (h⁻¹).1.1 * z * lowBlock g.1.1)) v) := by
  intro L _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hS ℓ hℓ huniq g h hg hh
  have hU := hS.1.unr
  have hnorm : ∀ (g : GU σ n) (h : GU σ n') (x : Matrix (Fin n') (Fin n) L),
      ω (g, h) * ρ x = ρ (h.1.1 * x * ((g.1)⁻¹ : GL (Fin n) L).1) * ω (g, h) := hS.1.norm
  have c1 : ∀ (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h →
      ∀ v, ℓ (ω (g, h) v) = ℓ (ω (g, h) s) * ℓ v := by
    intro g h hg hh
    refine huniq (ℓ.comp (ω (g, h))) (fun a ha v => ?_)
    have hm := (GlobalTheory.T.unitaryBorel_preserves_mixedModelLattice_lowerBlock L ϖ σ q hU n n' g⁻¹ h (isBorelU_inv_mixeq hg) hh).1 a ha
    show ℓ (ω (g, h) (ρ a v)) = ℓ (ω (g, h) v)
    rw [← Module.End.mul_apply, hnorm, Module.End.mul_apply]
    exact hℓ _ hm _
  refine ⟨c1 g h hg hh, fun z v => ?_⟩
  obtain ⟨a, ha, ha0, he⟩ := (GlobalTheory.T.unitaryBorel_preserves_mixedModelLattice_lowerBlock L ϖ σ q hU n n' g h⁻¹ hg (isBorelU_inv_mixeq hh)).2 z
  have key : ρ (embLow n' n z) * ω (g, h) = ω (g, h) * ρ ((h⁻¹).1.1 * embLow n' n z * g.1.1) := by
    rw [hnorm]
    congr 2
    simp [Matrix.mul_assoc]
  set E' := embLow n' n (lowBlock (h⁻¹).1.1 * z * lowBlock g.1.1) with hE'
  have h0 : locH σ δ (antiG L n) (antiG L n') a E' = 0 := by
    rw [locH_antiG]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_)
    by_cases hj : j.1 < n - n / 2
    · rw [ha0 i j hj, zero_mul]
    · rw [hE', embLow, dite_eq_right (by simp only [Fin.val_rev]; omega), map_zero, mul_zero]
  have hsplit : ρ (a + E') = ρ a * ρ E' := by
    rw [hS.1.rho_mul, h0]
    simp
  rw [← Module.End.mul_apply, key, Module.End.mul_apply, c1 g h hg hh, he, hsplit, Module.End.mul_apply, hℓ a ha]

end GlobalTheory.SphTheta
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.NoLiftTransfer

theorem jm_mul_jm (p q : ℕ) : Jm p q * Jm p q = 1 := by
  unfold Jm Formalism.UG.Jpq
  simp [Matrix.fromBlocks_multiply]

theorem conj_trace {p q : ℕ} {Z : Mat p q} (hZ : Z ∈ upq p q) : (starRingEnd ℂ) Z.trace = -Z.trace := by
  have h : Zᴴ * Jm p q + Jm p q * Z = 0 := hZ

  have h2 : Jm p q * Zᴴ * Jm p q + Z = 0 := by
    have h' := congrArg (fun X => Jm p q * X) h
    simpa [mul_add, ← mul_assoc, jm_mul_jm] using h'
  have h3 : (Jm p q * Zᴴ * Jm p q).trace + Z.trace = 0 := by rw [← Matrix.trace_add, h2, Matrix.trace_zero]
  rw [Matrix.trace_mul_comm, ← mul_assoc, jm_mul_jm, one_mul, Matrix.trace_conjTranspose] at h3
  rw [starRingEnd_apply]
  exact eq_neg_of_add_eq_zero_left h3

def invConj {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (u : A → B)
    (hb : Function.Bijective u) (hadd : ∀ x y, u (x + y) = u x + u y)
    (hsmul : ∀ (z : ℂ) x, u (z • x) = conj z • u x) : B →ₛₗ[starRingEnd ℂ] A where
  toFun := (Equiv.ofBijective u hb).symm
  map_add' x y := by
    apply hb.1
    rw [hadd]
    simp only [Equiv.ofBijective_apply_symm_apply]
  map_smul' z x := by
    apply hb.1
    rw [hsmul]
    simp only [Equiv.ofBijective_apply_symm_apply, Complex.conj_conj]

theorem invConj_apply {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (u : A → B)
    (hb : Function.Bijective u) (hadd : ∀ x y, u (x + y) = u x + u y)
    (hsmul : ∀ (z : ℂ) x, u (z • x) = conj z • u x) (x : A) : invConj u hb hadd hsmul (u x) = x :=
  hb.1 ((Equiv.ofBijective u hb).apply_symm_apply (u x))

theorem noLift_of_pairNo : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (ι σ Z : Type) (A : Mn V.rank → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) (p q : ℕ) (T₁ : GrpData p q) (R₁ : DSRep T₁) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (l₁ : Ix p q → ℚ) (c₁ : ℚ) (b₁ : Bool) (e₁ : Ix p q ≃ Fin V.rank) (u₁ : kfin M τ → R₁.HK.V), KTie R₁ M τ l₁ c₁ b₁ true e₁ u₁ → Side A pt κ (phiFr (M.fr τ) b₁ e₁) c₁ a₁ → PairNo a₁ R₁ → NoLift M τ A pt := by
  intro D V S M τ ι σ Z A pt κ p q T₁ R₁ a₁ l₁ c₁ b₁ e₁ u₁ hK hS hP

  have hsm : ∀ (z : ℂ) x, u₁ (z • x) = conj z • u₁ x := fun z x => by simpa [cjc] using hK.smul z x
  let w := invConj u₁ hK.bij hK.add hsm
  have hw_right : ∀ y, u₁ (w y) = y := fun y => (Equiv.ofBijective u₁ hK.bij).apply_symm_apply y
  have hw_left : ∀ v, w (u₁ v) = v := fun v => invConj_apply u₁ hK.bij hK.add hsm v
  intro U _ _ Q hQ

  let B : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V →ₛₗ[starRingEnd ℂ] U :=
    { toFun := fun P => (Q (κ.symm P)).comp w
      map_add' := fun P P' => by ext x; simp
      map_smul' := fun z P => by ext x; simp }
  have hB : ∀ P x, B P x = Q (κ.symm P) (w x) := fun _ _ => rfl
  have hinv : PInv a₁ R₁ B := by
    intro Y hY P x
    set t : ℂ := (c₁ : ℂ) * Y.trace with ht_def

    have ht : conj t = -t := by rw [ht_def, map_mul, conj_trace hY, map_ratCast, mul_neg]
    have hX : phiFr (M.fr τ) b₁ e₁ Y ∈ lieAt V τ := by rw [← hK.lie]; exact ⟨Y, hY, rfl⟩
    have hpol : PolDer A pt (phiFr (M.fr τ) b₁ e₁ Y) (κ.symm P) (κ.symm (a₁ Y P + t • P)) :=
      (hS.der Y hY _ _).2 (by simp only [LinearEquiv.apply_symm_apply, ht_def])
    have hvec : VecDer M τ (phiFr (M.fr τ) b₁ e₁ Y) (w x) (w (R₁.HK.act Y x + t • x)) :=
      (hK.der Y hY _ _).2 (by simp only [hw_right, ht_def])
    have h0 := hQ _ hX _ _ _ _ hpol hvec
    have e1 : Q (κ.symm (a₁ Y P + t • P)) (w x) = Q (κ.symm (a₁ Y P)) (w x) + t • Q (κ.symm P) (w x) := by
      rw [map_add (f := _), map_smul, map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    have e2 : Q (κ.symm P) (w (R₁.HK.act Y x + t • x)) =
        Q (κ.symm P) (w (R₁.HK.act Y x)) - t • Q (κ.symm P) (w x) := by
      rw [map_add (f := _), map_add (f := _), map_smulₛₗ, ht, map_smul, neg_smul, sub_eq_add_neg]
    rw [e1, e2] at h0
    rw [hB, hB, ← h0]
    abel
  have hB0 : B = 0 := hP U B hinv
  refine LinearMap.ext fun P => LinearMap.ext fun v => ?_
  have h1 := congrArg (fun F : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V →ₛₗ[starRingEnd ℂ] U => F (κ P) (u₁ v)) hB0
  simpa [hB, hw_left] using h1

end GlobalTheory.ArchRec.NoLiftTransfer

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

noncomputable section
namespace GlobalTheory.ArchRec.EnumBlocks

theorem signed_eq {p q : ℕ} {l₁ l₂ : List ℚ} (c : ℚ) (h₁ : l₁.length = p) (h₂ : l₂.length = q) :
    signed l₁ l₂ c = Finset.univ.image fun a : Ix p q => (ofBlocks l₁ l₂ a + c, a.isLeft) := by
  subst h₁ h₂
  ext ⟨x, b⟩
  simp only [signed, Finset.mem_union, List.mem_toFinset, List.mem_map, Prod.mk.injEq, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨y, hy, rfl, rfl⟩ | ⟨y, hy, rfl, rfl⟩)
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hy
      exact ⟨.inl i, by simp [ofBlocks], rfl⟩
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hy
      exact ⟨.inr i, by simp [ofBlocks], rfl⟩
  · rintro ⟨a | a, rfl, rfl⟩
    · exact Or.inl ⟨_, by simp [ofBlocks], rfl, by simp⟩
    · exact Or.inr ⟨_, by simp [ofBlocks], rfl, by simp⟩

theorem sameBlock_iff {p q : ℕ} (a b : Ix p q) : sameBlock a b ↔ b.isLeft = a.isLeft := by
  rcases a with a | a <;> rcases b with b | b <;> simp [sameBlock]

theorem card_filter_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (P : β → Prop) (Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ b, P (e b) ↔ Q b) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card :=
  (Finset.card_equiv e (fun b => by simp [h])).symm

theorem lowK_numbered {n p q : ℕ} {ε : Fin n → Bool} {lamM : Fin n → ℝ} (e : Ix p q ≃ Fin n)
    (hε : ∀ a, ε (e a) = a.isLeft) (R : Ix p q → Ix p q → Prop) (hR : ∀ a b, e a < e b ↔ R a b) (a : Ix p q)
    [DecidableRel R] :
    Formalism.QuantumDeterminants.lowK ε lamM (e a) = lamM (e a) +
      ((((Finset.univ.filter fun b => ¬ sameBlock a b ∧ R a b).card : ℝ) -
        ((Finset.univ.filter fun b => ¬ sameBlock a b ∧ R b a).card : ℝ)) / 2 -
       (((Finset.univ.filter fun b => sameBlock a b ∧ R a b).card : ℝ) -
        ((Finset.univ.filter fun b => sameBlock a b ∧ R b a).card : ℝ)) / 2) := by
  classical
  have hs : ∀ b, ε (e b) = ε (e a) ↔ sameBlock a b := fun b => by rw [hε, hε, sameBlock_iff]
  have hn : ∀ b, ε (e b) ≠ ε (e a) ↔ ¬ sameBlock a b := fun b => not_congr (hs b)
  have n1 := card_filter_equiv e (fun j => e a < j ∧ ε j ≠ ε (e a)) (fun b => ¬ sameBlock a b ∧ R a b)
    fun b => by rw [hR, hn]; exact and_comm
  have n2 := card_filter_equiv e (fun j => j < e a ∧ ε j ≠ ε (e a)) (fun b => ¬ sameBlock a b ∧ R b a)
    fun b => by rw [hR, hn]; exact and_comm
  have c1 := card_filter_equiv e (fun j => e a < j ∧ ε j = ε (e a)) (fun b => sameBlock a b ∧ R a b)
    fun b => by rw [hR, hs]; exact and_comm
  have c2 := card_filter_equiv e (fun j => j < e a ∧ ε j = ε (e a)) (fun b => sameBlock a b ∧ R b a)
    fun b => by rw [hR, hs]; exact and_comm
  simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, Formalism.REAL.rhoN, Formalism.REAL.rhoC]
  rw [n1, n2, c1, c2]
  ring

theorem core {n p q : ℕ} {L : Ix p q → ℚ} (hL : Function.Injective L) {c s : ℚ} (hs : s = 1 ∨ s = -1)
    {ε : Fin n → Bool} {lamM : Fin n → ℝ}
    (hE : IsEnum (Finset.univ.image fun a : Ix p q => (s * (L a + c), a.isLeft)) lamM ε) :
    ∃ e : Ix p q ≃ Fin n, IsOrd ε lamM L c (s : ℝ) e := by
  classical
  obtain ⟨hanti, r, hr, hS⟩ := hE
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hf : Function.Injective fun a : Ix p q => (s * (L a + c), a.isLeft) := fun a b h =>
    hL (add_right_cancel (mul_left_cancel₀ hs0 (congrArg Prod.fst h)))
  have hg : Function.Injective fun i => (r i, ε i) := fun i j h =>
    hanti.injective (by rw [hr, hr, show r i = r j from congrArg Prod.fst h])
  have ex : ∀ a : Ix p q, ∃ i, (r i, ε i) = (s * (L a + c), a.isLeft) := fun a => by
    have : (s * (L a + c), a.isLeft) ∈ Finset.univ.image fun i => (r i, ε i) := by
      rw [← hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 this
    exact ⟨i, hi⟩
  choose f hfi using ex
  have finj : Function.Injective f := fun a b h => hf (by
    show (s * (L a + c), a.isLeft) = (s * (L b + c), b.isLeft)
    rw [← hfi a, ← hfi b, h])
  have fsurj : Function.Surjective f := fun i => by
    have : (r i, ε i) ∈ Finset.univ.image fun a : Ix p q => (s * (L a + c), a.isLeft) := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 this
    exact ⟨a, hg ((hfi a).trans ha)⟩
  let e : Ix p q ≃ Fin n := Equiv.ofBijective f ⟨finj, fsurj⟩
  have he : ∀ a, (r (e a), ε (e a)) = (s * (L a + c), a.isLeft) := hfi
  have hε : ∀ a, ε (e a) = a.isLeft := fun a => congrArg Prod.snd (he a)
  have hr' : ∀ a, r (e a) = s * (L a + c) := fun a => congrArg Prod.fst (he a)
  have hlam : ∀ a, lamM (e a) = (s : ℝ) * ((L a + c : ℚ) : ℝ) := fun a => by
    rw [hr, hr']; push_cast; ring
  have hlt : ∀ a b, e a < e b ↔ s * L b < s * L a := fun a b => by
    have h0 : e a < e b ↔ lamM (e b) < lamM (e a) := ⟨fun h => hanti h, fun h => by
      by_contra hn
      exact absurd (hanti.antitone (not_lt.1 hn)) (not_le.2 h)⟩
    rw [h0, hlam, hlam]
    rw [← Rat.cast_mul, ← Rat.cast_mul, Rat.cast_lt, mul_add, mul_add, add_lt_add_iff_right]
  refine ⟨e, hε, hlam, fun a => ?_⟩
  rcases hs with rfl | rfl
  · rw [lowK_numbered e hε (fun a b => L b < L a) (fun a b => by simpa using hlt a b) a, hlam]
    simp only [blattner, rhoNC]
    push_cast
    ring
  · rw [lowK_numbered e hε (fun a b => L a < L b) (fun a b => by simpa using hlt a b) a, hlam]
    simp only [blattner, rhoNC]
    push_cast
    ring

theorem parOf_eq {p q : ℕ} {l₁ l₂ : List ℚ} (br cj : Bool) (c : ℚ) (h₁ : l₁.length = p) (h₂ : l₂.length = q) :
    parOf br cj l₁ l₂ c = Finset.univ.image fun a : Ix p q =>
      ((if br = cj then 1 else -1 : ℚ) * (ofBlocks l₁ l₂ a + c), a.isLeft) := by
  classical
  unfold parOf dualPar
  rw [signed_eq c h₁ h₂]
  split_ifs
  · simp
  · rw [Finset.image_image]
    refine Finset.image_congr fun a _ => ?_
    simp

theorem exists_isOrd (n p q : ℕ) (l₁ l₂ : List ℚ) (c : ℚ) (br cj : Bool) (ε : Fin n → Bool) (lamM : Fin n → ℝ)
    (h₁ : l₁.length = p) (h₂ : l₂.length = q) (hP : IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ))
    (hE : IsEnum (parOf br cj l₁ l₂ c) lamM ε) :
    ∃ e : Ix p q ≃ Fin n, IsOrd ε lamM (ofBlocks l₁ l₂) c (sg br cj) e := by
  rw [parOf_eq br cj c h₁ h₂] at hE
  have hs : (if br = cj then 1 else -1 : ℚ) = 1 ∨ (if br = cj then 1 else -1 : ℚ) = -1 := by
    split_ifs <;> simp
  have := core hP.1 hs hE
  have hc : (((if br = cj then 1 else -1 : ℚ)) : ℝ) = sg br cj := by
    unfold sg; split_ifs <;> simp
  rwa [hc] at this

end GlobalTheory.ArchRec.EnumBlocks
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
open GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift (NcGapGt NcGapGe minSig lamS lamT StepGap)
open GlobalTheory.Chain.ItPairCompare GlobalTheory.Chain.ParOfSizes GlobalTheory.Chain.ParOfNodeGap

namespace GlobalTheory.ArchRec.ParChain

theorem num_bound_two {n q m N : ℕ} (hq : q ≤ m) (hn : n ≤ N) (hm : 1 ≤ m) (hN : 8 * m ≤ N) :
    120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 2 * (N : ℝ) ^ 3 := by
  have hq' : (q : ℝ) ≤ m := by exact_mod_cast hq
  have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hN' : 8 * (m : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ 2 := by
    calc (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ ((3 : ℝ) / 2) := by gcongr
      _ ≤ (m : ℝ) ^ ((2 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hm' (by norm_num)
      _ = (m : ℝ) ^ 2 := Real.rpow_natCast _ _
  have h2 : 60 * (m : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by nlinarith
  calc 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (N : ℝ) * (m : ℝ) ^ 2 := by gcongr
    _ = 2 * (N : ℝ) * (60 * (m : ℝ) ^ 2) := by ring
    _ ≤ 2 * (N : ℝ) * (N : ℝ) ^ 2 := by gcongr
    _ = 2 * (N : ℝ) ^ 3 := by ring

theorem stepGap_of_gap {D : D7} (h : NodeGap D) (k : Fin D.R.m) : StepGap D k := by
  intro τ
  obtain ⟨N, hN, hgap⟩ := h
  set h₀ : ℝ := (D.R.t : ℝ) + 2 * (N : ℝ) ^ 3 + 1 with hh
  have hg : ∀ (i : ℕ) (h : i + 1 < D.R.m),
      h₀ ≤ (((D.hc τ).b ⟨i + 1, h⟩ - (D.hc τ).b ⟨i, by omega⟩ : ℚ) : ℝ) := by
    intro i h
    have := hgap τ ⟨i, by omega⟩ h
    rw [hh]
    exact_mod_cast this
  have hS : NcGapGe (lamS D k τ) h₀ := by
    rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hs
    obtain ⟨a, rfl, rfl⟩ := (mem_lamS k τ _ _).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamS k τ _ _).1 hy
    exact le_val_sub _ hg _ _ a b hs
  have hT : NcGapGe (lamT D k τ) h₀ := by
    rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hs
    obtain ⟨a, rfl, rfl⟩ := (mem_lamT k τ _ _).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamT k τ _ _).1 hy
    exact le_val_sub _ hg _ _ a b hs
  have hr : ∀ j, j ≤ D.R.m → D.R.rankY j ≤ N := fun j hj => by
    have := Nat.mul_le_mul_right D.R.t hj
    unfold Ranks.rankX' at hN
    unfold Ranks.rankY
    omega
  have h3 : 8 * D.R.m ≤ N := by
    have h8 : 8 ≤ D.R.t := by
      have := D.R.rank_add_five_le; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
    have := Nat.mul_le_mul_left D.R.m h8
    unfold Ranks.rankX' at hN
    omega
  have ht : (0 : ℝ) ≤ D.R.t := by positivity
  have h1 : (D.R.rankY ((k : ℕ) + 1) : ℝ) ^ 3 < h₀ := by
    have h2 : (D.R.rankY ((k : ℕ) + 1) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hr _ k.2
    have h3 := pow_le_pow_left₀ (by positivity) h2 3
    have h4 : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
    linarith
  have h2 := num_bound_two (minSig_lamS_le k τ) (hr _ k.2.le) (by have := D.R.two_le_m; omega) h3
  exact ⟨fun x hx y hy hs => h1.trans_le (hS x hx y hy hs), fun x hx y hy hs => h1.trans_le (hT x hx y hy hs),
    fun x hx y hy hs => le_trans (by linarith) (hS x hx y hy hs)⟩

theorem parChain : ∀ (D : D7) (k : Fin D.R.m) (τ : D.what₂.Tau), ∃ al be ga de : List ℚ, Centred D al be ga de ∧ parA (Ptw D) k τ = signed (al ++ be) (ga ++ de) (alT D k τ) ∧ parA (Ptw D) (k + 1) τ = signed (al ++ block D.R.t ++ de) (ga ++ be) (alS D k τ) := by
  intro D k τ
  obtain ⟨al, be, ga, de, hA, hb, h1, h2⟩ := exists_lists_chain k τ
  refine ⟨al, be, ga, de, ⟨hA, hb, fun hG => ?_⟩, eq_signed_iff.2 h1, eq_signed_iff.2 h2⟩
  have h := stepGap_of_gap hG k τ
  have hr : D.R.rankY ((k : ℕ) + 1) = D.R.rankY k + D.R.t := by simp only [Ranks.rankY]; ring
  rw [hr] at h
  refine (hypG_iff hA.2.2.2.2.2.2.1 (h1 ▸ card_lamS k τ)).2 ?_
  rwa [← h1, ← h2]

end GlobalTheory.ArchRec.ParChain

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_maximalCompact_of_maps_fockVector_to_fock : ∀ (n : ℕ) (ε : Fin n → Bool) (fr G : Matrix (Fin n) (Fin n) ℂ) (σ Z : Type) [Finite σ] (pt : MvPolynomial σ ℂ →ₗ[ℂ] (Z → ℂ)) (R : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ (Z → ℂ)) (L : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ (MvPolynomial σ ℂ)), IsUnit fr → frᴴ * Formalism.REAL.Jm ε * fr = G → Function.Injective pt → R 1 = 1 → (∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ g' ∈ Formalism.QuantumDeterminants.UH G, R (g * g') = R g * R g') → (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 → ∀ φ z, HasDerivAt (fun t : ℝ => R (NormedSpace.exp (t • X)) (pt φ) z) (pt (L X φ) z) 0) → (∀ k ∈ Formalism.REAL.Kset ε, ∀ φ, ∃ ψ, ψ.totalDegree ≤ φ.totalDegree ∧ R (fr⁻¹ * k * fr) (pt φ) = pt ψ) → (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 → (∃ j k, ε j ≠ ε k ∧ (fr * X * fr⁻¹) j k ≠ 0 ∧ (fr * X * fr⁻¹) k j ≠ 0) → ∀ φ : MvPolynomial σ ℂ, φ ≠ 0 → ∀ F : Submodule ℂ (MvPolynomial σ ℂ), FiniteDimensional ℂ F → ¬ ∀ m : ℕ, (L X ^ m) φ ∈ F) → ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ φ φ', φ ≠ 0 → pt φ' = R g (pt φ) → ∃ k ∈ Formalism.REAL.Kset ε, g = fr⁻¹ * k * fr := by
  first | exact @GlobalTheory.Chain.RealIt.CompactStab.mem_compact | exact GlobalTheory.Chain.RealIt.CompactStab.mem_compact | (intros; apply GlobalTheory.Chain.RealIt.CompactStab.mem_compact <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvalAtUnitVector

theorem ipM_self_eq_zero {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T : MMap M) (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (h0 : T v = 0) :
    ipM M μ 𝓕 T T = 0 := by
  by_cases h : ∃ c, IsMultIP M μ 𝓕 T T c
  · have h1 := (ipM_spec M μ 𝓕 T T h v v).2
    have h2 : (∏ τ, inner ℂ (v τ : M.H τ) (v τ : M.H τ)) = 1 :=
      Finset.prod_eq_one fun τ _ => by
        rw [inner_self_eq_norm_sq_to_K, hv τ]
        simp
    rw [h2, mul_one, h0] at h1
    rw [← h1]
    simp
  · unfold ipM
    exact dif_neg h

theorem evInj {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (he : R.models_HW)
    (hv : ∀ i σ, IsChosenExtremalVector R i σ (v₀ i σ)) : EvInj T R v₀ := by
  intro i σ _ x y hxy
  have h0 : (R.HW i σ).e (x - y) (v₀ i σ) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.2 hxy
  have h1 := (he i σ).2.2 (x - y) (x - y)
  rw [ipAt, ipM_self_eq_zero _ _ _ _ (v₀ i σ) (IsChosenExtremalVector.norm R (hv i σ)) h0, mul_zero] at h1
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h1)

end GlobalTheory.EvalAtUnitVector
end
