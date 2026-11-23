module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2316
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertValuesIffInertLabelsCarriedEigensystems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle238
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle164
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle322
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle480
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle557
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle380
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle594
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.UnitaryEmbeddingLine

variable {D : D7}

theorem tmul_mul_inc (α : AF D.host.F) (b x : D.host.E) :
    (α ⊗ₜ[D.host.F] b : AE D) * incA D x = α ⊗ₜ[D.host.F] (b * x) := by
  change (α ⊗ₜ[D.host.F] b) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x : AE D) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem exists_coeff {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0) (p : Fin c) :
    ∃ r : Fin B.rank → D.host.E, ∀ (y : Fin A.rank → D.host.E) (u : Fin c → D.host.E),
      r ⬝ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) = u p := by
  have hG : B.gramᴴ = B.gram := Matrix.ext fun i j => B.herm.eq _ _
  have h1 : d.aᴴ * B.gram * d.a = antiDiagonalSignGramMatrix c ε := d.gram
  have h2 : (frameMat B A d.ι)ᴴ * B.gram * d.a = 0 := d.perp
  have h3 : d.aᴴ * B.gram * frameMat B A d.ι = 0 := by
    have := congrArg Matrix.conjTranspose h2
    rw [Matrix.conjTranspose_zero, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hG,
      Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc] at this
    exact this
  have hκ : antiDiagonalSignGramMatrix c ε p.rev p ≠ 0 := by
    have := p.2
    have e : p.rev.1 + p.1 + 1 = c := by rw [Fin.val_rev]; omega
    simp only [antiDiagonalSignGramMatrix, if_pos e]
    split_ifs
    · exact hε
    · exact one_ne_zero
  refine ⟨(antiDiagonalSignGramMatrix c ε p.rev p)⁻¹ • (d.aᴴ * B.gram) p.rev, fun y u => ?_⟩
  have e : (d.aᴴ * B.gram) p.rev ⬝ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) =
      ((d.aᴴ * B.gram) *ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u)) p.rev := rfl
  rw [smul_dotProduct, e, mulVec_add, mulVec_mulVec, mulVec_mulVec, h1, h3, zero_mulVec, zero_add]
  have e2 : (antiDiagonalSignGramMatrix c ε *ᵥ u) p.rev = antiDiagonalSignGramMatrix c ε p.rev p * u p := by
    show ∑ q, antiDiagonalSignGramMatrix c ε p.rev q * u q = _
    refine Finset.sum_eq_single p (fun q _ hq => ?_) (by simp)
    have := p.2
    have hne : ¬ (p.rev.1 + q.1 + 1 = c) := by
      intro h; apply hq; apply Fin.ext; rw [Fin.val_rev] at h; omega
    simp only [antiDiagonalSignGramMatrix, if_neg hne, zero_mul]
  rw [e2, smul_eq_mul, inv_mul_cancel_left₀ hκ]

def formHom {R : Type} [CommRing R] {n : ℕ} (r : Fin n → R) : (Fin n → R) →+ R where
  toFun y := ∑ k, y k * r k
  map_zero' := by simp
  map_add' x y := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

def lineHom {R : Type} [CommRing R] {n : ℕ} (a : Fin n → R) : R →+ (Fin n → R) where
  toFun s := fun k => s * a k
  map_zero' := by funext k; simp
  map_add' x y := by funext k; simp only [Pi.add_apply, add_mul]

theorem form_line {K R : Type} [CommRing K] [CommRing R] (f : K →+* R) {n : ℕ} (r a : Fin n → K) (h : r ⬝ᵥ a = 1) (s : R) :
    formHom (fun k => f (r k)) (fun k => s * f (a k)) = s := by
  show ∑ k, s * f (a k) * f (r k) = s
  simp only [mul_assoc, ← map_mul]

  rw [← Finset.mul_sum, ← map_sum]
  have : ∑ k, a k * r k = 1 := by
    rw [← h, dotProduct]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [this, map_one, mul_one]

theorem col_eq {K : Type} [CommRing K] {n k c : ℕ} (M : Matrix (Fin n) (Fin k) K) (a : Matrix (Fin n) (Fin c) K) (p : Fin c)
    (b : K) : (fun i => b * a i p) = M *ᵥ 0 + a *ᵥ Pi.single p b := by
  funext k; simp [mul_comm]

theorem line_mp {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D)
    (S : Set D.host.E) (I : GlobalTheory.SeeSaw.FI D) (hε : ε ≠ 0) (hI : ∀ a ∈ S, ∀ b ∈ 𝔟 p, a * b ∈ I) (s : AE D)
    (h : (fun k => s * incA D (d.a k p)) ∈ GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v)) : s ∈ GlobalTheory.SeeSaw.idV I v := by
  obtain ⟨r, hr⟩ := exists_coeff d hε p
  have key : GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v) ≤ (GlobalTheory.SeeSaw.idV I v).comap (formHom fun k => incA D (r k)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hαv, a, ha, x, ⟨y0, -, u, hu, hx⟩, rfl⟩
    have e : ∑ k, ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * x k) : AE D) * incA D (r k) =
        (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * u p) := by
      rw [Finset.sum_congr rfl fun k _ => tmul_mul_inc (pairA D.host.F 0 α) (a * x k) (r k),
        ← TensorProduct.tmul_sum, ← hr y0 u, ← hx, dotProduct, Finset.mul_sum]
      exact congrArg _ (Finset.sum_congr rfl fun k _ => by ring)
    have h2 : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * u p) ∈ GlobalTheory.SeeSaw.idV I v :=
      AddSubgroup.subset_closure ⟨α, hα, hαv, _, hI a ha _ (hu p), rfl⟩
    rw [← e] at h2
    exact h2
  have h1 := hr 0 (Pi.single p 1)
  rw [← col_eq, Pi.single_eq_same] at h1
  simp only [one_mul] at h1
  have := AddSubgroup.mem_comap.1 (key h)
  rwa [form_line (incA D) r (fun k => d.a k p) h1 s] at this

theorem line_mpr {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D)
    (S : Set D.host.E) (I : GlobalTheory.SeeSaw.FI D)
    (hI' : ∀ C : D.host.E → Prop, (∀ a ∈ S, ∀ b ∈ 𝔟 p, C (a * b)) → (∀ x y, C x → C y → C (x + y)) → ∀ z ∈ I, C z)
    (s : AE D) (h : s ∈ GlobalTheory.SeeSaw.idV I v) :
    (fun k => s * incA D (d.a k p)) ∈ GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v) := by
  have key : GlobalTheory.SeeSaw.idV I v ≤ (GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v)).comap (lineHom fun k => incA D (d.a k p)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hαv, z, hz, rfl⟩
    refine hI' (fun z => ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] z : AE D) ∈
      (GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v)).comap (lineHom fun k => incA D (d.a k p))) ?_ ?_ z hz
    · intro a ha b hb
      refine AddSubgroup.mem_comap.2 (AddSubgroup.subset_closure ⟨α, hα, hαv, a, ha, fun k => b * d.a k p,
        ⟨0, Λ.zero_mem, Pi.single p b, fun q => ?_, col_eq _ _ p b⟩, ?_⟩)
      · by_cases hq : q = p
        · subst hq; rwa [Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne hq]; exact (𝔟 q).zero_mem
      · funext k
        exact (tmul_mul_inc _ _ _).trans (congrArg _ (mul_assoc _ _ _))
    · intro x y hx hy
      rw [TensorProduct.tmul_add]
      exact add_mem hx hy
  exact AddSubgroup.mem_comap.1 (key h)

theorem line_gen {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D)
    (S : Set D.host.E) (I : GlobalTheory.SeeSaw.FI D) (hε : ε ≠ 0) (hI : ∀ a ∈ S, ∀ b ∈ 𝔟 p, a * b ∈ I)
    (hI' : ∀ C : D.host.E → Prop, (∀ a ∈ S, ∀ b ∈ 𝔟 p, C (a * b)) → (∀ x y, C x → C y → C (x + y)) → ∀ z ∈ I, C z)
    (s : AE D) :
    (fun k => s * incA D (d.a k p)) ∈ GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV I v :=
  ⟨line_mp d Λ 𝔟 p v S I hε hI s, line_mpr d Λ 𝔟 p v S I hI' s⟩

theorem embedding_line_mem_lattice_iff : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε), ε ≠ 0 → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D) (s : AE D), (((fun k => s * incA D (d.a k p)) ∈ latV B (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV (𝔟 p) v) ∧ ((fun k => s * incA D (d.a k p)) ∈ latA B (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA * 𝔟 p) v)) := by
  intro D A B c ε d hε Λ 𝔟 p v s
  refine ⟨line_gen d Λ 𝔟 p v {1} (𝔟 p) hε ?_ ?_ s, line_gen d Λ 𝔟 p v {a | a ∈ D.host.AA} _ hε ?_ ?_ s⟩
  · rintro a rfl b hb; rwa [one_mul]
  · intro C h _ z hz
    have := h 1 rfl z hz
    rwa [one_mul] at this
  · intro a ha b hb; exact FractionalIdeal.mul_mem_mul ha hb
  · intro C h h' z hz
    exact FractionalIdeal.mul_induction_on hz h h'

end GlobalTheory.AscFin.UnitaryEmbeddingLine

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.ChiGrid
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.UnitaryEmbeddingColumns

open GlobalTheory.FinPl GlobalTheory.SeeSaw

theorem gram_star {D : D7} (B : HSp D) (i j : Fin B.rank) : star (B.gram i j) = B.gram j i := by
  have := B.herm.eq (B.frame i) (B.frame j)
  simpa [HSpace.gram, starRingEnd_apply] using this

theorem incA_mul_tmul' {D : D7} (e : D.host.E) (y : AF D.host.F) (z : D.host.E) :
    incA D e * (y ⊗ₜ[D.host.F] z) = y ⊗ₜ[D.host.F] (e * z) := by
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) * (y ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem tmul_mul_incA {D : D7} (y : AF D.host.F) (t e : D.host.E) :
    (y ⊗ₜ[D.host.F] t) * incA D e = y ⊗ₜ[D.host.F] (t * e) := by
  show (y ⊗ₜ[D.host.F] t) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]



theorem mem_idV_of_mem {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D)
    (q : Fin c) (b : AE D)
    (h : (fun k => b * incA D (d.a k q)) ∈ GlobalTheory.FinPl.latV B (d.lat Λ 𝔟) (· = v)) : b ∈ GlobalTheory.SeeSaw.idV (𝔟 q) v := by
  classical
  set r : Fin c := q.rev with hr
  set κ : D.host.E := antiDiagonalSignGramMatrix c ε r q with hκdef
  have hcond : ∀ p : Fin c, (r.1 + p.1 + 1 = c ↔ p = q) := by
    intro p
    have := q.2; have := p.2
    rw [hr, Fin.val_rev, Fin.ext_iff]; omega
  have hκ : κ ≠ 0 := by
    rw [hκdef, antiDiagonalSignGramMatrix, ite_eq_left ((hcond q).2 rfl)]
    split_ifs
    · exact hε
    · exact one_ne_zero
  let π : Fin B.rank → D.host.E := fun j => κ⁻¹ * ∑ l, star (d.a l r) * B.gram l j
  have hπa : ∀ p, ∑ j, π j * d.a j p = if p = q then 1 else 0 := by
    intro p
    have e := congrFun (congrFun d.gram r) p
    simp only [Matrix.mul_apply, Formalism.UG.cT, transpose_apply, map_apply] at e
    have e2 : ∑ j, π j * d.a j p = κ⁻¹ * antiDiagonalSignGramMatrix c ε r p := by
      rw [← e, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [π]
      rw [mul_assoc]
      congr 2
    rw [e2]
    split_ifs with hp
    · subst hp; rw [← hκdef]; exact inv_mul_cancel₀ hκ
    · rw [antiDiagonalSignGramMatrix, ite_eq_right (fun h' => hp ((hcond p).1 h')), mul_zero]
  have hπM : ∀ i, ∑ j, π j * frameMat B A d.ι j i = 0 := by
    intro i
    have e := congrFun (congrFun d.perp i) r
    simp only [Matrix.mul_apply, Formalism.UG.cT, transpose_apply, map_apply, Matrix.zero_apply] at e
    have hsig : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x := fun _ => rfl
    have e3 : ∑ j, π j * frameMat B A d.ι j i =
        κ⁻¹ * ∑ j, ∑ l, star (d.a l r) * B.gram l j * frameMat B A d.ι j i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [π]
      rw [mul_assoc, Finset.sum_mul]
    rw [e3]
    have e4 : ∑ j, ∑ l, star (d.a l r) * B.gram l j * frameMat B A d.ι j i =
        star (∑ l, (∑ x, (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι x i) * B.gram x l) * d.a l r) := by
      simp only [star_sum, star_mul', Finset.sum_mul, hsig, star_star, gram_star]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e4, e, star_zero, mul_zero]
  let Φ : (Fin B.rank → AE D) →+ AE D :=
    { toFun := fun Y => ∑ k, incA D (π k) * Y k
      map_zero' := by simp
      map_add' := fun Y Z => by simp [mul_add, Finset.sum_add_distrib] }
  have hΦ : ∀ Y ∈ latV B (d.lat Λ 𝔟) (· = v), Φ Y ∈ idV (𝔟 q) v := by
    intro Y hY
    induction hY using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, hαv, a, ha, x, hx, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      obtain ⟨y, -, u, hu, rfl⟩ := hx
      have e : Φ (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) i)) =
          pairA D.host.F 0 α ⊗ₜ[D.host.F] u q := by
        show ∑ k, incA D (π k) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) k)) = _
        simp only [incA_mul_tmul', one_mul]
        rw [← TensorProduct.tmul_sum]
        congr 1
        have h1 : ∑ k, π k * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) k =
            ∑ i, (∑ j, π j * frameMat B A d.ι j i) * y i + ∑ p, (∑ j, π j * d.a j p) * u p := by
          simp only [Pi.add_apply, mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
            Finset.sum_mul]
          congr 1
          · rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          · rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        rw [h1]
        simp only [hπM, hπa, zero_mul, Finset.sum_const_zero, zero_add, ite_mul, one_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [e]
      exact AddSubgroup.subset_closure ⟨α, hα, hαv, u q, hu q, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add Y Z _ _ hY hZ => rw [map_add]; exact add_mem hY hZ
    | neg Y _ hY => rw [map_neg]; exact neg_mem hY
  have key := hΦ _ h
  have e : Φ (fun k => b * incA D (d.a k q)) = b := by
    show ∑ k, incA D (π k) * (b * incA D (d.a k q)) = b
    have : ∀ k, incA D (π k) * (b * incA D (d.a k q)) = b * incA D (π k * d.a k q) := fun k => by
      rw [map_mul (incA D) (π k) (d.a k q)]; ring

    rw [Finset.sum_congr rfl (fun k _ => this k), ← Finset.mul_sum, ← map_sum, hπa q, ite_eq_left rfl, map_one, mul_one]
  rwa [e] at key



theorem mem_of_mem_idV {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D)
    (q : Fin c) (b : AE D)
    (h : b ∈ GlobalTheory.SeeSaw.idV (𝔟 q) v) : (fun k => b * incA D (d.a k q)) ∈ GlobalTheory.FinPl.latV B (d.lat Λ 𝔟) (· = v) := by
  classical
  let Ψ : AE D →+ (Fin B.rank → AE D) := AddMonoidHom.pi fun k => AddMonoidHom.mulRight (incA D (d.a k q))
  have hle : idV (𝔟 q) v ≤ (latV B (d.lat Λ 𝔟) (· = v)).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hαv, t, ht, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨α, hα, hαv, 1, Set.mem_singleton _, d.a *ᵥ Pi.single q t, ?_, ?_⟩
    · refine ⟨0, Λ.zero_mem, Pi.single q t, fun p => ?_, by simp⟩
      by_cases hp : p = q
      · subst hp; simpa using ht
      · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
    · funext k
      show (pairA D.host.F 0 α ⊗ₜ[D.host.F] t) * incA D (d.a k q) = _
      rw [tmul_mul_incA, one_mul]
      congr 1
      rw [mulVec_single, Pi.smul_apply, op_smul_eq_mul, Matrix.col_apply, mul_comm]
  exact hle h

theorem mem_latV_iff {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D)
    (q : Fin c) (b : AE D) :
    (fun k => b * incA D (d.a k q)) ∈ GlobalTheory.FinPl.latV B (d.lat Λ 𝔟) (· = v) ↔ b ∈ GlobalTheory.SeeSaw.idV (𝔟 q) v :=
  ⟨mem_idV_of_mem d hε Λ 𝔟 v q b, mem_of_mem_idV d Λ 𝔟 v q b⟩

end GlobalTheory.UnitaryEmbeddingColumns

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.CarriesOne

open GlobalTheory.Hk3

theorem heckePolyOf_coeff_inj : ∀ (n q : ℕ), q ≠ 0 → ∀ a b : ℕ → ℂ, Formalism.L2.Col.heckePolyOf n q a = Formalism.L2.Col.heckePolyOf n q b → ∀ k ≤ n, a k = b k := by
  intro n q hq a b h k hk
  have hc := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f k) h
  simp only [Formalism.L2.Col.heckePolyOf, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at hc
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos (Finset.mem_range.2 (Nat.lt_succ_of_le hk)),
    if_pos (Finset.mem_range.2 (Nat.lt_succ_of_le hk))] at hc
  have h0 : ((-1 : ℂ) ^ k * (q : ℂ) ^ (k * (k - 1) / 2)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hq))
  exact mul_left_cancel₀ h0 hc

theorem parts_eq_of_rowLabels : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ SF, GlobalTheory.Hk3.IsSF R SF → ∀ (c c' : Pl D.host.E → List ℤ → ℂ), (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.IsLab (Yc D 0) P d → c P (dualLab d) = c' P (dualLab d)) → GlobalTheory.Hk3.EEc R SF c = GlobalTheory.Hk3.EEc R SF c' ∧ ∀ i, GlobalTheory.Hk3.Wcc R SF i c = GlobalTheory.Hk3.Wcc R SF i c' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hSF c c' key
  obtain ⟨hQ, hgood, hoff, -⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev
  refine ⟨?_, fun i => ?_⟩
  · obtain ⟨n, hβ⟩ := hC.lev.βY 0 (by have := D.R.two_le_m; omega)
    have hlev := fun (P : Pl D.host.E) (hP : Good R A.μ0 P) =>
      GlobalTheory.T.level_operators_at_prime_off_level_datum (Yc D 0) (R.βY 0) (R.ΛY 0) ((D.host.g 0 * D.host.g 1) ^ n) (R.dat0 R.triv) hβ P
        (by
          intro h
          push_cast at h
          exact (hgood A.μ0 P hP).1 (P.isPrime.mem_of_pow_mem _ (by exact_mod_cast h)))
        (by
          intro PP hPP
          refine hP PP (hPP.imp id ?_)
          intro h
          exact absurd h (Finset.notMem_empty _))
    unfold GlobalTheory.Hk3.EEc partDual
    congr 1
    ext U
    rw [LabDet.mem_partFull, LabDet.mem_partFull]
    refine and_congr_right fun _ => forall_congr' fun P => forall_congr' fun d => forall_congr' fun B => imp_congr_right fun hB => ?_
    have hP : Good R A.μ0 P := by
      obtain ⟨_, _, _, _, ho, _⟩ := hB
      exact (hoff SF hSF P).1 ho
    rw [key P d hP ⟨B, (((hlev P hP).2.1 SF d B).1 hB).2⟩]
  · obtain ⟨n, hβ⟩ := hC.lev.βW i
    have hlev := fun (P : Pl D.host.E) (hP : Good R A.μ0 P) =>
      GlobalTheory.T.level_operators_at_prime_off_level_datum (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ P
        (by rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top)
        (by
          intro PP hPP
          refine hP PP (hPP.imp id ?_)
          intro h
          exact absurd h (Finset.notMem_empty _))
    have keyW : ∀ P, Good R A.μ0 P → ∀ d, IsLab (Wc D i) P d → c P d = c' P d := by
      intro P hP d hd
      have h := key P (dualLab d) hP ((GlobalTheory.LabEq.isLab_W_iff R F (s := 0) hC i P d hP).1.1 hd)
      rwa [GlobalTheory.CarriedHecke.dualLab_dualLab] at h
    have hpf : partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c =
        partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c' := by
      ext U
      rw [LabDet.mem_partFull, LabDet.mem_partFull]
      refine and_congr_right fun _ => forall_congr' fun P => forall_congr' fun d => forall_congr' fun B => imp_congr_right fun hB => ?_
      have hP : Good R A.μ0 P := by
        obtain ⟨_, _, _, _, ho, _⟩ := hB
        exact (hoff SF hSF P).1 ho
      rw [keyW P hP d ⟨B, (((hlev P hP).2.1 SF d B).1 hB).2⟩]
    unfold Wcc
    rw [hpf]

theorem parts_eq_of_carries : GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → UpInj R.toRealDat → (∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c') := by

  intro hHowe hCusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hW e hInert hUp p c c' hc hc'
  obtain ⟨hC, hSF, hE, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW e
  have hS := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCusp R.toRealDat
  have hL := GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hCusp D
  have hTwo := GlobalTheory.VmTwo.twoSided_goodInert hHowe R F hL hW e hS
  have hinj : ∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0 :=
    fun _ w _ h => hUp A3.A.μ0 (h.trans (map_zero _).symm)
  have hpol := GlobalTheory.CarriedHecke.hecke_polys_of_carries R F hL hok hW e hS hinj
  have hr : (Yc D 0).rank = D.R.r := by
    show (D.sp.Y (min 0 D.R.m)).rank = D.R.r
    rw [Nat.zero_min, D.sp.Y_rank 0 (Nat.zero_le _)]
    simp [Ranks.rankY, Ranks.r]
  have hs : ∀ P, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P → Formalism.DivisionValues.conjPl P ≠ P → ∀ k ≤ (Yc D 0).rank,
      c P (dualLab (splitLab (Yc D 0).rank k)) = c' P (dualLab (splitLab (Yc D 0).rank k)) := by
    intro P hP hcP k hk
    obtain ⟨P0, h0, rfl, hq⟩ := GlobalTheory.T.goodSplitPlace_of_family_prime_base_tuple R F hW e P hP hcP
    have h1 := (hpol p c hc P0 h0).1
    have h2 := (hpol p c' hc' P0 h0).1
    rw [hr] at hk ⊢
    exact heckePolyOf_coeff_inj D.R.r _ hq _ _ (h1.symm.trans h2) k hk
  have hE0 : GlobalTheory.Hk3.EEc R.toRealDat R.SF c ≠ ⊥ := hE c ▸ hc.1
  have hE0' : GlobalTheory.Hk3.EEc R.toRealDat R.SF c' ≠ ⊥ := hE c' ▸ hc'.1
  have ksplit := GlobalTheory.T.heckeEigenvalues_eq_of_dual_enlarging_labels_split R.toRealDat F.lv2 hC R.SF hSF c c' hE0 hE0' hs
  let i0 : Fin D.R.m := ⟨0, by have := D.R.two_le_m; omega⟩
  have kin := (GlobalTheory.InertValLab.inert_vals_iff_labels R F hL hok hW e hS hTwo hInert hinj i0 p p c c' hc hc').1 (fun _ => rfl)
  have key : ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P → GlobalTheory.Hk3.IsLab (Yc D 0) P d → c P (dualLab d) = c' P (dualLab d) := by
    intro P d hP hd
    by_cases hcP : Formalism.DivisionValues.conjPl P = P
    · apply kin P _ hP hcP
      rw [(GlobalTheory.LabEq.isLab_W_iff R.toRealDat F.lv2 (s := 0) hC i0 P _ hP).1, GlobalTheory.CarriedHecke.dualLab_dualLab]
      exact hd
    · exact ksplit P hP hcP d hd
  obtain ⟨h1, h2⟩ := parts_eq_of_rowLabels R.toRealDat F.lv2 hC R.SF hSF c c' key
  exact ⟨by rw [hE, hE, h1], fun i => by rw [hWc, hWc, h2 i]⟩

end GlobalTheory.CarriesOne

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weil_realPoint_fockVector_positiveDefinite_det : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → (∀ τ, (BT τ)ᴴ * gramAt D T τ * BT τ = 1) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ + (S.rank : ℚ) / 2) → (∀ τ, (e₂ τ : ℚ) = -(b τ + (T.rank : ℚ) / 2)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, om (g, h) (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f P) = (∏ τ, (compAt θ τ (Formalism.L2.Theta.mt S g)).det ^ e₂ τ * (compAt θ τ (Formalism.L2.Theta.mt T h)).det ^ e₁ τ) • pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f (GlobalTheory.CompactHowe.substF (fun τ => (BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) (fun τ => (((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ)⁻¹)ᵀ) P) := by
  first | exact @GlobalTheory.RealFockPos.om_pureTensorO_pos | exact GlobalTheory.RealFockPos.om_pureTensorO_pos | (intros; apply GlobalTheory.RealFockPos.om_pureTensorO_pos <;> assumption)
end
