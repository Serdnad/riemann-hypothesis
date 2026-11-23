module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle527
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootsMinpolyPhi
public import Mathlib.RepresentationTheory.Coinduced
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle079
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivationProdPow
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PderivEqZeroOfColOp
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle205
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerIntertwinesHeckeOperators
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle206
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle207
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle208
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle199
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

noncomputable section

namespace GlobalTheory.SeriesSupport

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp Formalism.MainNotions.ArithmeticCylinders Formalism.BasicNotions Formalism.CyclotomicNorms
open scoped Classical

section Dual

variable {g : ℕ} [Fact g.Prime]

theorem phi_conj (L : LabelDatum g) (x : Fbar g) : GalSer.phi L (starRingAut : ℂ ≃+* ℂ) x = x⁻¹ := by
  by_cases hx : x = 0
  · rw [hx, GalSer.phi_zero, inv_zero]
  apply GalSer.teich_injective L
  rw [GalSer.teich_phi]
  have h1 : ‖L.teich x‖ = 1 := (L.teich.isOfFinOrder (GalSer.finOrder hx)).norm_eq_one
  have h2 : L.teich x⁻¹ = (L.teich x)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ hx, map_one])
  rw [h2, Complex.inv_eq_conj h1]
  rfl

theorem roots_reverse {K : Type} [Field K] (s : Multiset K) (hs : (0 : K) ∉ s) :
    ((s.map fun x => X - C x).prod.reverse).roots = s.map (·⁻¹) := by
  apply GlobalTheory.DualLabel.roots_reverse_prod <;> assumption

theorem rel_dual (L : LabelDatum g) {f : (ZMod g)[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    GalSer.Rel L (starRingAut : ℂ ≃+* ℂ) f (C (f.coeff 0)⁻¹ * f.reverse) := by
  refine ⟨?_, ?_⟩
  · rw [Monic, leadingCoeff_mul, leadingCoeff_C, reverse_leadingCoeff, trailingCoeff_eq_coeff_zero h0,
      inv_mul_cancel₀ h0]
  · have hz : (0 : Fbar g) ∉ rootsBar f := fun h => by
      rw [GalSer.mem_rootsBar hm.ne_zero, ← coeff_zero_eq_aeval_zero'] at h
      exact h0 ((map_eq_zero _).1 h)
    have e : f.reverse.map (algebraMap (ZMod g) (Fbar g)) = (f.map (algebraMap (ZMod g) (Fbar g))).reverse := by
      rw [reverse, reverse, reflect_map, natDegree_map]
    have hf := (IsAlgClosed.splits (f.map (algebraMap (ZMod g) (Fbar g)))).eq_prod_roots_of_monic (hm.map _)
    rw [rootsBar, Polynomial.map_mul, map_C, roots_C_mul _ (by simpa using h0), e, hf]
    simp only [phi_conj]
    exact roots_reverse _ hz

end Dual

local instance factTypePrime (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

abbrev LocRep (D : D7) (k : Fin 2) (n : ℕ) : Type 1 := Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k])

variable (D : D7)
  (σ : D.ntypes.Par → ∀ k, D.nd.PlG k → LocRep D k D.R.r)
  (ΩV : D.what₂.Tup → ℕ → ∀ k, D.nd.PlG k → LocRep D k D.R.nV)
  (ιV : ∀ μ j k v, D.what₂.Mt μ j →ₗ[ℂ] ΩV μ j k v)
  (ΩX : D.what₂.Tup → ∀ k, D.nd.PlG k → LocRep D k D.R.rankX')
  (ιX : ∀ μ k v, D.what₂.Amb μ →ₛₗ[starRingEnd ℂ] ΩX μ k v)

end GlobalTheory.SeriesSupport
end
end

section

open NumberField IsDedekindDomain
open Formalism.UG (GLint)

noncomputable section
namespace GlobalTheory.GLintCover

section
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

theorem v_eq_one_of_mul {x y : v.adicCompletion F} (hx : x ∈ Formalism.UG.Ov F v) (hy : y ∈ Formalism.UG.Ov F v)
    (hxy : x * y = 1) : Valued.v x = 1 := by
  have h1 : Valued.v x * Valued.v y = 1 := by rw [← map_mul, hxy, map_one]
  have hy1 : Valued.v y ≤ 1 := hy
  have hx1 : Valued.v x ≤ 1 := hx
  refine le_antisymm hx1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v x * Valued.v y := h1.symm
    _ ≤ Valued.v x := mul_le_of_le_one_right' hy1

theorem det_v {n : ℕ} {X : GL (Fin n) (v.adicCompletion F)} (hX : X ∈ GLint (Fin n) (Formalism.UG.Ov F v)) :
    Valued.v (X : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = 1 := by
  apply GlobalTheory.valued_det_eq_one_of_glint <;> assumption

variable {n : ℕ} {ϖ : v.adicCompletion F} {a : Fin n → ℤ}

end
end GlobalTheory.GLintCover

noncomputable section
namespace GlobalTheory.GLintCover

section Count
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

variable {ϖ : v.adicCompletion F} {a : Fin n → ℤ}

end Count
end GlobalTheory.GLintCover

noncomputable section
namespace GlobalTheory.GLintCover

section Main
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
variable {ϖ : v.adicCompletion F} {a : Fin n → ℤ}

end Main

end GlobalTheory.GLintCover
end
end
end
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FockMinorExtremal

open MvPolynomial GlobalTheory.JointHarm GlobalTheory.JointHarm.Minor GlobalTheory.Capelli

section General

variable {A : Type} [CommRing A] [Algebra ℂ A] (D : Derivation ℂ A A) {n l : ℕ}
  (y : Matrix (Fin n) (Fin l) A)

theorem der_minor {a b : Fin l} (hab : a ≤ b) (hD : ∀ c k, D (y c k) = if k = b then y c a else 0)
    {m : ℕ} (row : Fin m → Fin n) (h : m ≤ l) :
    D (y.submatrix row (Fin.castLE h)).det =
      (if a = b then (if a.1 < m then (1 : ℂ) else 0) else 0) • (y.submatrix row (Fin.castLE h)).det := by
  rw [← Matrix.det_transpose, derivation_det]
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, hD]
  by_cases hb : b.1 < m
  · rw [Finset.sum_eq_single (⟨b.1, hb⟩ : Fin m)]
    · have e : Fin.castLE h ⟨b.1, hb⟩ = b := rfl
      simp only [e, if_true]
      split_ifs with h1 h2
      · subst h1
        rw [one_smul]
        congr 1
        exact Matrix.updateRow_eq_self _ _
      · exact absurd (h1 ▸ hb) h2
      · have hlt : a.1 < b.1 := lt_of_le_of_ne hab fun e => h1 (Fin.ext e)
        have hne : (⟨a.1, hlt.trans hb⟩ : Fin m) ≠ ⟨b.1, hb⟩ := fun e => by
          rw [Fin.ext_iff] at e; simp at e; omega
        rw [zero_smul]
        refine Matrix.det_zero_of_row_eq hne ?_
        rw [Matrix.updateRow_self, Matrix.updateRow_ne hne]
        rfl
    · intro i _ hi
      refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
      rw [Matrix.updateRow_self, if_neg fun e : Fin.castLE h i = b => hi (Fin.ext (congrArg Fin.val e :))]
    · simp
  · have h0 : (if a = b then (if a.1 < m then (1 : ℂ) else 0) else 0) = 0 := by
      split_ifs with h1 h2
      · exact absurd (h1 ▸ h2) hb
      · rfl
      · rfl
    rw [h0, zero_smul]
    refine Finset.sum_eq_zero fun i _ => Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
    rw [Matrix.updateRow_self, if_neg fun e : Fin.castLE h i = b => hb (e ▸ i.2)]

theorem sum_rows (α : Fin l → ℕ) (hα : Antitone α) (a : Fin l) :
    ∑ i : Fin l, ((α i - nextRow α i : ℕ) : ℂ) * (if a.1 < i.1 + 1 then 1 else 0) = α a := by
  let f : ℕ → ℕ := fun i => if h : i < l then α ⟨i, h⟩ else 0
  have hf : Antitone f := by
    refine antitone_nat_of_succ_le fun i => ?_
    simp only [f]
    split_ifs with h1 h2 h2
    · exact hα (by simp [Fin.le_def])
    · omega
    · exact Nat.zero_le _
    · exact le_rfl
  have h := telescope f hf a l
  have hl : f l = 0 := by simp [f]
  rw [if_pos a.2.le, hl, ← Fin.sum_univ_eq_sum_range
    (fun i => ((f i - f (i + 1) : ℕ) : ℂ) * (if a.1 < i + 1 then 1 else 0))] at h
  have e1 : ∀ i : Fin l, f i = α i := fun i => by simp [f, i.2]
  have e2 : ∀ i : Fin l, f (i + 1) = nextRow α i := fun i => rfl
  simpa only [e1, e2, Nat.cast_zero, sub_zero] using h

theorem der_minorProd (α : Fin l → ℕ) (hα : Antitone α) (row : ∀ i : Fin l, Fin (i.1 + 1) → Fin n)
    {a b : Fin l} (hab : a ≤ b) (hD : ∀ c k, D (y c k) = if k = b then y c a else 0) :
    D (minorProd α y row) = (if a = b then (α a : ℂ) else 0) • minorProd α y row := by
  rw [minorProd, derivation_prod_pow D _ _ _ _ fun i => der_minor D y hab hD (row i) i.2]
  congr 1
  split_ifs with h
  · exact sum_rows α hα a
  · simp

theorem der_minorProd_zero (α : Fin l → ℕ) (row : ∀ i : Fin l, Fin (i.1 + 1) → Fin n)
    (hD : ∀ i c k, D (y (row i c) k) = 0) : D (minorProd α y row) = 0 := by
  rw [minorProd, derivation_prod_pow D _ _ _ (fun _ => 0) fun i => ?_]
  · simp
  · rw [zero_smul, derivation_det]
    refine Finset.sum_eq_zero fun j _ => Matrix.det_eq_zero_of_row_eq_zero j fun k => ?_
    rw [Matrix.updateRow_self, Matrix.submatrix_apply, hD]

end General

theorem minorProd_ne_zero {σ : Type} {n l : ℕ} (z : Fin n × Fin l → σ) (hz : Function.Injective z)
    (α : Fin l → ℕ) (row : ∀ i : Fin l, Fin (i.1 + 1) → Fin n) (hrow : ∀ i, Function.Injective (row i)) :
    minorProd α (Matrix.of fun c k => (X (z (c, k)) : MvPolynomial σ ℂ)) row ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _
    (lead_ne_zero (fun w : Fin (i.1 + 1) × Fin l => z (row i w.1, w.2))
      (hz.comp ((hrow i).prodMap Function.injective_id)) le_rfl i.2)

variable {p q n : ℕ}

def vPlus (p q n : ℕ) : Fin p × Fin n → Ln p q n 0 := fun w => (.inl w.1, .inl w.2)

def vMinus (p q n : ℕ) : Fin q × Fin n → Ln p q n 0 := fun w => (.inr w.1, .inl w.2)

theorem vPlus_inj : Function.Injective (vPlus p q n) := fun u w h => by
  simpa [vPlus, Prod.ext_iff] using h

theorem vMinus_inj : Function.Injective (vMinus p q n) := fun u w h => by
  simpa [vMinus, Prod.ext_iff] using h

theorem act_plus (i j : Fin p) (P : Pol p q n 0) :
    fockAct1 p q n 0 (Eab (.inl i) (.inl j)) P =
      rowDer (vPlus p q n) i j P + (if i = j then (n : ℂ) / 2 else 0) • P := by
  rw [isSide_one.1, mixedOp_apply, ← rowOp_eq_rowDer, rowOp_apply]
  simp [zA, vPlus, cPair]

theorem act_minus (i j : Fin q) (P : Pol p q n 0) :
    fockAct1 p q n 0 (Eab (.inr j) (.inr i)) P =
      -rowDer (vMinus p q n) i j P - (if i = j then (n : ℂ) / 2 else 0) • P := by
  rw [isSide_one.2, mixedOp_apply, ← rowOp_eq_rowDer, rowOp_apply]
  simp [zD, vMinus, cPair, eq_comm]

theorem der_plus (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) (hp : Antitone ap) {i j : Fin p}
    (hij : i ≤ j) :
    rowDer (vPlus p q n) i j (delta hn ap am) = (if i = j then (ap i : ℂ) else 0) • delta hn ap am := by
  rw [delta, Derivation.leibniz, der_minorProd _ (zPlus p q n) ap hp _ hij
    fun c k => rowDer_X _ vPlus_inj i j k c, der_minorProd_zero _ (zMinus p q n) am _ fun _ c k => ?_]
  · simp [mul_comm]
  · rw [← rowOp_eq_rowDer, rowOp_apply]
    simp [zMinus, vPlus, pderiv_X, Pi.single_apply]

theorem der_minus (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) (hm : Antitone am) {i j : Fin q}
    (hij : i ≤ j) :
    rowDer (vMinus p q n) i j (delta hn ap am) = (if i = j then (am i : ℂ) else 0) • delta hn ap am := by
  rw [delta, Derivation.leibniz, der_minorProd _ (zMinus p q n) am hm _ hij
    fun c k => rowDer_X _ vMinus_inj i j k c, der_minorProd_zero _ (zPlus p q n) ap _ fun _ c k => ?_]
  · simp
  · rw [← rowOp_eq_rowDer, rowOp_apply]
    simp [zPlus, vMinus, pderiv_X, Pi.single_apply]

theorem lower (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) :
    KilledByLower (fockAct1 p q n 0) (delta hn ap am) := by
  intro a b
  rw [GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.fockAct1_lower, neg_eq_zero, GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.lowerOp]
  refine Finset.sum_eq_zero fun c _ => ?_
  have h1 : pderiv ((.inr b, .inl c) : Ln p q n 0) (minorProd ap (zPlus p q n) (topRows (by omega))) = 0 :=
    der_minorProd_zero _ _ _ _ fun _ _ _ => pderiv_X_of_ne (by simp)
  have h2 : pderiv ((.inl a, .inl c) : Ln p q n 0) (minorProd am (zMinus p q n) (botRows (by omega))) = 0 :=
    der_minorProd_zero _ _ _ _ fun _ _ _ => pderiv_X_of_ne (by simp)
  rw [delta, Derivation.leibniz, h1, smul_zero, add_zero, smul_eq_mul, Derivation.leibniz, pderiv_swap, h2,
    map_zero, smul_zero, zero_add, smul_eq_mul]
  by_cases hc : c.1 < p
  · rw [der_minorProd_zero (pderiv ((.inr b, .inl c) : Ln p q n 0)) (zMinus p q n) am (botRows (by omega))
      fun i d _ => pderiv_X_of_ne ?_,
      zero_mul]
    have := i.2
    simp only [botRows, ne_eq, Prod.mk.injEq, Sum.inl.injEq, Fin.ext_iff]
    omega
  · rw [der_minorProd_zero (pderiv ((.inl a, .inl c) : Ln p q n 0)) (zPlus p q n) ap (topRows (by omega))
      fun i d _ => pderiv_X_of_ne ?_,
      mul_zero]
    have := i.2
    have := d.2
    simp only [topRows, ne_eq, Prod.mk.injEq, Sum.inl.injEq, Fin.ext_iff]
    omega

theorem delta_extremal : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am → delta hn ap am ≠ 0 ∧ delta hn ap am ∈ wtSub (fockAct1 p q n 0) (wtExt n ap am) ∧ (∀ i j : Fin p, i < j → fockAct1 p q n 0 (Eab (Sum.inl i) (Sum.inl j)) (delta hn ap am) = 0) ∧ (∀ i j : Fin q, i < j → fockAct1 p q n 0 (Eab (Sum.inr j) (Sum.inr i)) (delta hn ap am) = 0) ∧ KilledByLower (fockAct1 p q n 0) (delta hn ap am) := by
  intro p q n hn ap am hp hm
  refine ⟨mul_ne_zero ?_ ?_, ?_, fun i j h => ?_, fun i j h => ?_, lower hn ap am⟩
  · exact minorProd_ne_zero (fun w => vPlus p q n w.swap) (vPlus_inj.comp Prod.swap_injective) ap _
      fun i c d h => by simpa [topRows, Fin.ext_iff] using h
  · exact minorProd_ne_zero (fun w => vMinus p q n w.swap) (vMinus_inj.comp Prod.swap_injective) am _
      fun i c d h => by simpa [botRows, Fin.ext_iff] using h
  · simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, Sum.forall, sub_eq_zero]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [act_plus, der_plus hn ap am hp le_rfl]
      simp [wtExt, add_smul]
    · rw [act_minus, der_minus hn ap am hm le_rfl]
      simp [wtExt, sub_smul]
  · rw [act_plus, der_plus hn ap am hp h.le]
    simp [h.ne]
  · rw [act_minus, der_minus hn ap am hm h.le]
    simp [h.ne]

end GlobalTheory.FockMinorExtremal

end
end

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.exists_locallyConstant_kum_cup_coboundary_of_norm_surj : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  (∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 → ∃ x : L, Algebra.norm K x = c) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧ ∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g := by
  first | exact @GlobalTheory.cup_kummer_coboundary_of_norms | exact GlobalTheory.cup_kummer_coboundary_of_norms | (intros; apply GlobalTheory.cup_kummer_coboundary_of_norms <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

theorem _root_.GlobalTheory.T.siegel_function_transformation : ∀ (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) (τ : ℍ), admitted c x → sg c x (γ • τ) = sg c (act x γ) τ := by
  first | exact @GlobalTheory.Sieg.sg_smul | exact GlobalTheory.Sieg.sg_smul | (intros; apply GlobalTheory.Sieg.sg_smul <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

namespace GlobalTheory.KZ

theorem isDiam_mul_comm_mod_Gam (N l d d' : ℕ) (σ σ' : SL(2, ℤ)) (h : IsDiam N l d σ) (h' : IsDiam N l d' σ') :
    ∃ g : SL(2, ℤ), g ∈ Gam N l ∧ σ' * σ = g * (σ * σ') := by
  obtain ⟨⟨h0, h1⟩, -⟩ := h
  obtain ⟨⟨h0', h1'⟩, -⟩ := h'
  refine ⟨σ' * σ * (σ * σ')⁻¹, ⟨?_, ?_⟩, by group⟩
  · set a : CongruenceSubgroup.Gamma0 N := ⟨σ, h0⟩ with ha
    set b : CongruenceSubgroup.Gamma0 N := ⟨σ', h0'⟩ with hb
    have hu : (CongruenceSubgroup.Gamma0Map N).toHomUnits (b * a * (a * b)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul,
        mul_comm ((CongruenceSubgroup.Gamma0Map N).toHomUnits b), mul_inv_cancel]
    have h3 : b * a * (a * b)⁻¹ ∈ CongruenceSubgroup.Gamma1' N := by
      rw [CongruenceSubgroup.Gamma1_mem', ← MonoidHom.coe_toHomUnits, hu, Units.val_one]
    exact (CongruenceSubgroup.Gamma1_mem N _).2 ((CongruenceSubgroup.Gamma1_to_Gamma0_mem _).1 h3)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1' h1) (Subgroup.inv_mem _ (Subgroup.mul_mem _ h1 h1'))

end GlobalTheory.KZ
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.atkinLehner_intertwines_hecke_operators : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (a a' : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → MF k (N * l) (ch χ) a → MF k (N * l) (ch χ⁻¹) a' → qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) → (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs (To k (ch χ q) q a)) = (ch χ q : ℂ) • qs (To k (ch χ⁻¹ q) q a')) ∧ slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs (Uo l a)) = (ch χ l : ℂ) • qs (Uo l a') := by
  first | exact @GlobalTheory.EisM.AtkinLehner.alHecke | exact GlobalTheory.EisM.AtkinLehner.alHecke | (intros; apply GlobalTheory.EisM.AtkinLehner.alHecke <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.principalSeriesCongruenceSubgroup_mul_closed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, a * b ∈ grp ψ := by
  first | exact @GlobalTheory.PsType.grp_mul_closed | exact GlobalTheory.PsType.grp_mul_closed | (intros; apply GlobalTheory.PsType.grp_mul_closed <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem dep_eq_sub (l : ℕ) (a : ℕ → ℂ) : dep l a = a + (-1 : ℂ) • Vo l (Uo l a) := by
  funext n
  simp only [dep, Vo, Uo, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [Nat.mul_div_cancel' h]; ring
  · ring

theorem depletion_mf : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → l.Prime → l ∣ L → (∀ d, χ (d + L) = χ d) → MF k L χ a → MF k L χ (Uo l a) ∧ MF k (L * l) χ (dep l a) := by
  intro k L l χ a hk hl hlL hχ ha
  have haL : MF k (L * l) χ a := ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k L χ).2.2.2.2.1 (L * l) a (dvd_mul_right L l) ha)
  have hU : MF k L χ (Uo l a) := GlobalTheory.T.coeffHeckeUOperator_lowers_level k L l χ a hk hl hlL hχ haL
  refine ⟨hU, ?_⟩
  have hV : MF k (L * l) χ (Vo l (Uo l a)) := (GlobalTheory.T.coeffHeckeVOperator_raises_level k L l χ (Uo l a) hl.pos).1 hU
  have hV' := ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (L * l) χ).2.2.1 (-1 : ℂ) _ hV).1
  rw [dep_eq_sub]
  exact ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (L * l) χ).2.1 _ _ haL hV').1

end GlobalTheory
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.sturm_sum_over_characters_eq_zero : ∀ (k L N : ℕ), 0 < L → N ∣ L → ∃ B : ℕ, ∀ a : DirichletCharacter ℂ N → ℕ → ℂ, (∀ ε, MF k L (ch ε) (a ε)) → (∀ n < B, (∑ ε, a ε) n = 0) → ∑ ε, a ε = 0 := by
  first | exact @GlobalTheory.EisM.sturm_sum_coef_zero | exact GlobalTheory.EisM.sturm_sum_coef_zero | (intros; apply GlobalTheory.EisM.sturm_sum_coef_zero <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.galB_mem_kummer_invariant_set : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ b ∈ X.B N l w, X.galB l s b ∈ X.B N l w := by
  first | exact @GlobalTheory.KZ.StabGal.galB_mem_B | exact GlobalTheory.KZ.StabGal.galB_mem_B | (intros; apply GlobalTheory.KZ.StabGal.galB_mem_B <;> assumption)
end
