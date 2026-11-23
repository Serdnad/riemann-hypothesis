module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle011
public import Mathlib.CategoryTheory.Category.Basic
import Aesop.Frontend.Tactic
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle005
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.FlatFactor.KerEngine

def pullSB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) : SB Y →ₗ[ℂ] SB X where
  toFun Φ := ⟨Φ.1 ∘ e, Φ.2.1.comp_continuous e.continuous, Φ.2.2.comp_homeomorph e⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pullSB_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (Φ : SB Y) (x : X) :
    (pullSB e Φ).1 x = Φ.1 (e x) := rfl

section Trip
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']

abbrev Rest (ev it : Finset (m × m')) := {e : m × m' // e ∉ it ∧ e ∉ ev}

def toTrip (ev it : Finset (m × m')) (β t : Matrix m m' k) :
    (Rest ev it → k) × ({e // e ∈ ev} → k) × ({e // e ∈ it} → k) :=
  (fun i => t i.1.1 i.1.2, fun i => t i.1.1 i.1.2 - β i.1.1 i.1.2, fun i => t i.1.1 i.1.2)

def ofTrip (ev it : Finset (m × m')) (β : Matrix m m' k)
    (x : (Rest ev it → k) × ({e // e ∈ ev} → k) × ({e // e ∈ it} → k)) : Matrix m m' k :=
  Matrix.of fun r q => if h : (r, q) ∈ it then x.2.2 ⟨(r, q), h⟩
    else if h' : (r, q) ∈ ev then β r q + x.2.1 ⟨(r, q), h'⟩ else x.1 ⟨(r, q), h, h'⟩

theorem ofTrip_toTrip (ev it : Finset (m × m')) (β t : Matrix m m' k) : ofTrip ev it β (toTrip ev it β t) = t := by
  ext r q
  simp only [ofTrip, toTrip, Matrix.of_apply]
  split_ifs <;> ring

theorem toTrip_ofTrip (ev it : Finset (m × m')) (hd : Disjoint ev it) (β : Matrix m m' k)
    (x : (Rest ev it → k) × ({e // e ∈ ev} → k) × ({e // e ∈ it} → k)) : toTrip ev it β (ofTrip ev it β x) = x := by
  obtain ⟨x₀, x₁, x₂⟩ := x
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext i
  · have h := i.2
    simp only [toTrip, ofTrip, Matrix.of_apply, dif_neg h.1, dif_neg h.2]
  · have h : i.1 ∉ it := Finset.disjoint_left.mp hd i.2
    simp only [toTrip, ofTrip, Matrix.of_apply, dif_neg h, dif_pos i.2]
    ring
  · simp only [toTrip, ofTrip, Matrix.of_apply, dif_pos i.2]

variable [TopologicalSpace k] [IsTopologicalRing k]

def trip (ev it : Finset (m × m')) (hd : Disjoint ev it) (β : Matrix m m' k) :
    Matrix m m' k ≃ₜ (Rest ev it → k) × ({e // e ∈ ev} → k) × ({e // e ∈ it} → k) where
  toFun := toTrip ev it β
  invFun := ofTrip ev it β
  left_inv := ofTrip_toTrip ev it β
  right_inv := toTrip_ofTrip ev it hd β
  continuous_toFun := by
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_) <;> refine continuous_pi fun i => ?_
    · exact continuous_id.matrix_elem _ _
    · exact (continuous_id.matrix_elem _ _).sub continuous_const
    · exact continuous_id.matrix_elem _ _
  continuous_invFun := by
    refine continuous_matrix fun r q => ?_
    simp only [ofTrip, Matrix.of_apply]
    split_ifs
    · exact (continuous_apply _).comp (continuous_snd.comp continuous_snd)
    · exact continuous_const.add ((continuous_apply _).comp (continuous_fst.comp continuous_snd))
    · exact (continuous_apply _).comp continuous_fst

theorem trip_apply (ev it : Finset (m × m')) (hd : Disjoint ev it) (β t : Matrix m m' k) :
    trip ev it hd β t = toTrip ev it β t := rfl

end Trip

end GlobalTheory.FlatFactor.KerEngine

namespace GlobalTheory.FlatFactor.KerEngine
open GlobalTheory.FlatFactor

section Laws
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']

theorem sum_single_apply (it : Finset (m × m')) (a : m × m' → k) (r : m) (q : m') :
    (∑ e ∈ it, Matrix.single e.1 e.2 (a e)) r q = if (r, q) ∈ it then a (r, q) else 0 := by
  rw [Matrix.sum_apply]
  have : ∀ e : m × m', Matrix.single e.1 e.2 (a e) r q = if (r, q) = e then a e else 0 := by
    rintro ⟨x, y⟩
    simp only [Matrix.single_apply, Prod.mk.injEq]
    split_ifs <;> aesop
  simp_rw [this, Finset.sum_ite_eq]

theorem toTrip_add (ev it : Finset (m × m')) (hd : Disjoint ev it) (β t : Matrix m m' k) (a : {e // e ∈ it} → k) :
    toTrip ev it β (t + ∑ e ∈ it, Matrix.single e.1 e.2 (if h : e ∈ it then a ⟨e, h⟩ else 0)) =
      toTrip ev it β t + (0, 0, a) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext i
  · have h := i.2
    simp only [toTrip, Matrix.add_apply, sum_single_apply, h.1, if_false, add_zero,
      Pi.add_apply, Pi.zero_apply] <;> simp
  · have h : i.1 ∉ it := Finset.disjoint_left.mp hd i.2
    simp only [toTrip, Matrix.add_apply, sum_single_apply, h, if_false, add_zero,
      Pi.add_apply, Pi.zero_apply] <;> simp
  · simp only [toTrip, Matrix.add_apply, sum_single_apply, i.2, if_true, dif_pos,
      Pi.add_apply, Pi.zero_apply, zero_add] <;> simp

theorem ofTrip_zero (ev it : Finset (m × m')) (β : Matrix m m' k) (x₀ : Rest ev it → k) (a : {e // e ∈ it} → k) :
    ofTrip ev it β (x₀, 0, a) = fill ev it β (ofTrip ev it β (x₀, 0, 0)) a := by
  ext r q
  simp only [ofTrip, fill, Matrix.of_apply]
  split_ifs <;> simp

end Laws

theorem kerRed_of_laws : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it : Finset (m × m')), Disjoint ev it → (∀ (b : m × m' → k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (∑ e ∈ ev, b e * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) → (∀ (a : m × m' → k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + ∑ e ∈ it, Matrix.single e.1 e.2 (a e))) → l Θ' = l Θ) → GlobalTheory.FlatFactor.KerRed ν ev it β l := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν m m' _ _ _ _ M _ _ l β ev it hd h1 h2 Θ hΘ
  let e := trip (k := k) ev it hd β
  let l' := l ∘ₗ pullSB e
  have hback : pullSB e (pullSB e.symm Θ) = Θ := by
    ext t
    simp [pullSB_apply]
  have key := GlobalTheory.CoinvSB.kernel k ψ ν hψc hψ1 hν (Rest ev it) {x // x ∈ ev} {x // x ∈ it} M l' ?_ ?_
    (pullSB e.symm Θ) ?_
  · simpa [l', hback] using key
  · intro b Φ Φ' hΦ
    refine h1 (fun e => if h : e ∈ ev then b ⟨e, h⟩ else 0) (pullSB e Φ) (pullSB e Φ') fun t => ?_
    rw [pullSB_apply, pullSB_apply, hΦ]
    congr 3
    simp only [e, trip_apply, toTrip, dotProduct]
    rw [← Finset.sum_coe_sort ev]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [i.2]
  · intro a Φ Φ' hΦ
    refine h2 (fun e => if h : e ∈ it then a ⟨e, h⟩ else 0) (pullSB e Φ) (pullSB e Φ') fun t => ?_
    rw [pullSB_apply, pullSB_apply, hΦ]
    simp only [e, trip_apply]
    rw [toTrip_add ev it hd β t a]
  · intro x₀
    have hr := hΘ (ofTrip ev it β (x₀, 0, 0))
    simp only [red] at hr
    rw [← hr]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [pullSB_apply]
    rw [← ofTrip_zero]
    rfl

end GlobalTheory.FlatFactor.KerEngine
end
end

section

open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

noncomputable section

namespace GlobalTheory.HeckeShift

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

abbrev IntCos (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :=
  {c : GL (Fin n) k ⧸ KO k (Fin n) // ∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k]}


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem int_mul {A B : Matrix (Fin n) (Fin n) k} (hA : ∀ i j, A i j ∈ 𝒪[k]) (hB : ∀ i j, B i j ∈ 𝒪[k]) (i j : Fin n) :
    (A * B) i j ∈ 𝒪[k] := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hA i l) (hB l j)

theorem ord_det_of_mem_KO {κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) :
    ord k (Matrix.GeneralLinearGroup.det κ) = 0 := by
  obtain ⟨g, rfl⟩ := hκ
  apply ord_eq_zero
  have h1 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
      algebraMap 𝒪[k] k (Matrix.GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)

theorem out_smul (y : GL (Fin n) k) (c : GL (Fin n) k ⧸ KO k (Fin n)) :
    ∃ κ ∈ KO k (Fin n), ((y • c).out : GL (Fin n) k) = y * c.out * κ := by
  refine ⟨(y * c.out)⁻¹ * (y • c).out, ?_, by group⟩
  have h : (QuotientGroup.mk (y * c.out) : GL (Fin n) k ⧸ KO k (Fin n)) = y • c := by
    conv_rhs => rw [← QuotientGroup.out_eq' c]
    rfl
  exact QuotientGroup.eq.1 (h.trans (QuotientGroup.out_eq' _).symm)

theorem int_out_smul {y : GL (Fin n) k} (hy : y ∈ KO k (Fin n)) (c : IntCos k n) (i j : Fin n) :
    ((y • c.1).out : GL (Fin n) k).1 i j ∈ 𝒪[k] := by
  obtain ⟨κ, hκ, e⟩ := out_smul y c.1
  rw [e, Units.val_mul, Units.val_mul]
  exact int_mul (int_mul ((SplitFlip.mem_KO_iff y).1 hy).1 c.2) ((SplitFlip.mem_KO_iff κ).1 hκ).1 i j

def smulEquiv {y : GL (Fin n) k} (hy : y ∈ KO k (Fin n)) : IntCos k n ≃ IntCos k n where
  toFun c := ⟨y • c.1, int_out_smul hy c⟩
  invFun c := ⟨y⁻¹ • c.1, int_out_smul (inv_mem hy) c⟩
  left_inv c := Subtype.ext (inv_smul_smul y c.1)
  right_inv c := Subtype.ext (smul_inv_smul y c.1)


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem diag_mul_upper {A B : Matrix (Fin n) (Fin n) k} (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hA i j h, zero_mul]
    · rw [hB j i h, mul_zero]
  · simp


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem diag_ne_zero {b : GL (Fin n) k} (hb : b ∈ borel k (Fin n)) (i : Fin n) : (b : Matrix (Fin n) (Fin n) k) i i ≠ 0 := by
  have h := Matrix.det_of_upperTriangular (M := (b : Matrix (Fin n) (Fin n) k)) (fun i j h => (mem_borel k).1 hb i j h)
  have hd : (b : Matrix (Fin n) (Fin n) k).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero b
  rw [h] at hd
  exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ _)

end GlobalTheory.HeckeShift

namespace GlobalTheory.HeckeShift

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def diagU {b : GL (Fin n) k} (hb : b ∈ borel k (Fin n)) (i : Fin n) : kˣ := Units.mk0 _ (diag_ne_zero hb i)

theorem exists_borel_mul (h : GL (Fin n) k) : ∃ b ∈ borel k (Fin n), ∃ x ∈ KO k (Fin n), h = b * x := by
  obtain ⟨b, hbT, x, hx, e⟩ := iwasawa_blockTriangular k (Fin n) (fun i => (i : ℕ)) h
  exact ⟨b, (mem_borel k).2 fun i j hij => hbT (show (j : ℕ) < i from hij), x, hx, e⟩

theorem sph_borel_mul {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (hφ : IsBorelSph k γ φ) (hγ : ∀ i, γ i ≠ 0)
    {b : GL (Fin n) k} (hb : b ∈ borel k (Fin n)) (h : GL (Fin n) k) :
    φ (b * h) = (∏ i, γ i ^ ord k (diagU hb i)) * φ h := by
  obtain ⟨b', hb', x, hx, rfl⟩ := exists_borel_mul h
  have hbb : b * b' ∈ borel k (Fin n) := mul_mem hb hb'
  rw [← mul_assoc, hφ.1 _ x hx, hφ.1 _ x hx, hφ.2 b' hb' (diagU hb') fun i => rfl,
    hφ.2 (b * b') hbb (fun i => diagU hb i * diagU hb' i) fun i => ?_, ← Finset.prod_mul_distrib]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [ord_mul, zpow_add₀ (hγ i)]
  · rw [Units.val_mul, Units.val_mul]
    exact diag_mul_upper ((mem_borel k).1 hb) ((mem_borel k).1 hb') i

end GlobalTheory.HeckeShift

namespace GlobalTheory.HeckeShift

theorem hasSum_hecke_shift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ X : ℂ, (∀ i : Fin n, ‖(resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X‖ < 1) → ∀ g : GL (Fin n) k, HasSum (fun c : {c : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k])} => X ^ (ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ (g * c.1.out)) ((∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) * φ g) := by
  intro k _ _ _ _ n γ φ hφ hγ X hX g
  obtain ⟨b, hb, x, hx, rfl⟩ := exists_borel_mul g
  have hI := (GlobalTheory.T.hasSum_heckeSeries_borelSpherical_integralCosets k n γ φ hφ X hX).mul_left (∏ i, γ i ^ ord k (diagU hb i))
  have key : ∀ c : IntCos k n,
      X ^ (ord k (Matrix.GeneralLinearGroup.det (smulEquiv (inv_mem hx) c).1.out)).toNat *
          φ (b * x * (smulEquiv (inv_mem hx) c).1.out) =
        (∏ i, γ i ^ ord k (diagU hb i)) * (X ^ (ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ c.1.out) := by
    intro c
    obtain ⟨κ, hκ, e⟩ := out_smul x⁻¹ c.1
    have e' : (smulEquiv (inv_mem hx) c).1.out = x⁻¹ * c.1.out * κ := e
    have hd : ord k (Matrix.GeneralLinearGroup.det (x⁻¹ * c.1.out * κ)) =
        ord k (Matrix.GeneralLinearGroup.det c.1.out) := by
      rw [map_mul, map_mul, ord_mul, ord_mul, ord_det_of_mem_KO (inv_mem hx), ord_det_of_mem_KO hκ]
      ring
    rw [e', hd, show b * x * (x⁻¹ * c.1.out * κ) = b * c.1.out * κ by group, hφ.1 _ κ hκ,
      sph_borel_mul hφ hγ hb]
    ring
  have h1 : HasSum ((fun c : IntCos k n => X ^ (ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat *
      φ (b * x * c.1.out)) ∘ smulEquiv (inv_mem hx))
      ((∏ i, γ i ^ ord k (diagU hb i)) * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) := by
    have hf : ((fun c : IntCos k n => X ^ (ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat *
        φ (b * x * c.1.out)) ∘ smulEquiv (inv_mem hx)) = fun c : IntCos k n => (∏ i, γ i ^ ord k (diagU hb i)) *
          (X ^ (ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ c.1.out) := funext key
    rw [hf]
    exact hI
  have h2 := (Equiv.hasSum_iff (smulEquiv (inv_mem hx))).1 h1
  rw [hφ.1 b x hx, hφ.2 b hb (diagU hb) fun i => rfl, mul_comm]
  exact h2

end GlobalTheory.HeckeShift
end
end

section

open Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory

theorem hsNormSq_eq_sum_stdBasis {V H : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (A : V →L[ℂ] H) :
    hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ V i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem sum_norm_sq_le_hsNormSq {V H : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (A : V →L[ℂ] H) {ι : Type} [Fintype ι] (v : ι → V) (hv : Orthonormal ℂ v) :
    ∑ i, ‖A (v i)‖ ^ 2 ≤ hsNormSq A := by
  set e := stdOrthonormalBasis ℂ V with he
  set f := stdOrthonormalBasis ℂ H
  have key : ∀ (x : V) (y : H), ‖⟪y, A x⟫_ℂ‖ = ‖⟪x, (ContinuousLinearMap.adjoint A) y⟫_ℂ‖ := by
    intro x y
    rw [← ContinuousLinearMap.adjoint_inner_left, norm_inner_symm]
  calc ∑ i, ‖A (v i)‖ ^ 2
      = ∑ i, ∑ j, ‖⟪f j, A (v i)⟫_ℂ‖ ^ 2 := by
        simp_rw [f.sum_sq_norm_inner_right]
    _ = ∑ j, ∑ i, ‖⟪v i, (ContinuousLinearMap.adjoint A) (f j)⟫_ℂ‖ ^ 2 := by
        rw [Finset.sum_comm]
        simp_rw [key]
    _ ≤ ∑ j, ‖(ContinuousLinearMap.adjoint A) (f j)‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => hv.sum_inner_products_le _
    _ = ∑ j, ∑ i, ‖⟪e i, (ContinuousLinearMap.adjoint A) (f j)⟫_ℂ‖ ^ 2 := by
        simp_rw [e.sum_sq_norm_inner_right]
    _ = ∑ i, ∑ j, ‖⟪f j, A (e i)⟫_ℂ‖ ^ 2 := by
        rw [Finset.sum_comm]
        simp_rw [key]
    _ = hsNormSq A := by
        rw [hsNormSq_eq_sum_stdBasis, ← he]
        simp_rw [f.sum_sq_norm_inner_right]

end GlobalTheory
end

section

open scoped InnerProductSpace

namespace GlobalTheory.CompactRep

theorem dense_finite_vectors (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [SecondCountableTopology K] (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : K →* H →L[ℂ] H)
    (hiso : ∀ k x, ‖π k x‖ = ‖x‖) (hcont : ∀ x, Continuous fun k => π k x) :
    Dense {v : H | ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧
      ∀ k, ∀ x ∈ S, π k x ∈ S} := by
  let N : Submodule ℂ H :=
    { carrier := {v : H | ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧
        ∀ k, ∀ x ∈ S, π k x ∈ S}
      add_mem' := by
        rintro a b ⟨S, hS, ha, hSs⟩ ⟨T, hT, hb, hTs⟩
        refine ⟨S ⊔ T, inferInstance, Submodule.add_mem_sup ha hb, ?_⟩
        intro k x hx
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
        rw [map_add (f := _)]
        exact Submodule.add_mem_sup (hSs k y hy) (hTs k z hz)
      zero_mem' := ⟨⊥, inferInstance, Submodule.zero_mem _, by
        intro k x hx
        rw [Submodule.mem_bot] at hx ⊢
        rw [hx, map_zero]⟩
      smul_mem' := by
        rintro c a ⟨S, hS, ha, hSs⟩
        exact ⟨S, hS, S.smul_mem c ha, hSs⟩ }
  have hNst : ∀ k, ∀ a ∈ N, π k a ∈ N := by
    rintro k a ⟨S, hS, ha, hSs⟩
    exact ⟨S, hS, hSs k a ha, hSs⟩
  have hinner : ∀ k a b, ⟪π k a, π k b⟫_ℂ = ⟪a, b⟫_ℂ := fun k a b =>
    (LinearIsometry.mk (π k).toLinearMap (hiso k)).inner_map_map a b
  have hinv : ∀ k a, π k (π k⁻¹ a) = a := by
    intro k a
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  have hOst : ∀ k, ∀ w ∈ Nᗮ, π k w ∈ Nᗮ := by
    intro k w hw
    rw [Submodule.mem_orthogonal] at hw ⊢
    intro a ha
    rw [← hinv k a, hinner]
    exact hw _ (hNst _ a ha)
  have hbot : Nᗮ = ⊥ := by
    by_contra hne
    haveI : Nontrivial Nᗮ := Submodule.nontrivial_iff_ne_bot.2 hne
    let ρ : K →* (Nᗮ →L[ℂ] Nᗮ) :=
      { toFun := fun k => ((π k).comp Nᗮ.subtypeL).codRestrict Nᗮ (fun w => hOst k w w.2)
        map_one' := by
          ext w
          simp
        map_mul' := by
          intro k l
          ext w
          show π (k * l) w = π k (π l w)
          rw [map_mul, ContinuousLinearMap.mul_apply] }
    have hρ : ∀ k (w : Nᗮ), ((ρ k w : Nᗮ) : H) = π k w := fun k w => rfl
    obtain ⟨S, hS0, hSf, hSs⟩ := exists_finiteDimensional_invariant K Nᗮ ρ
      (fun k w => hiso k w) (fun w => (hcont w).subtype_mk _)
    apply hS0
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hwN : (w : H) ∈ N := by
      refine ⟨S.map Nᗮ.subtype, inferInstance, ⟨w, hw, rfl⟩, ?_⟩
      rintro k x ⟨y, hy, rfl⟩
      exact ⟨ρ k y, hSs k y hy, rfl⟩
    have h0 : ⟪(w : H), (w : H)⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 w.2 _ hwN
    exact Subtype.ext (inner_self_eq_zero.1 h0)
  exact Submodule.dense_iff_topologicalClosure_eq_top.2
    (Submodule.topologicalClosure_eq_top_iff.2 hbot)

theorem dense_isKFin (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) : Dense {v : H | Formalism.MainNotions.S.IsKFin ε σ v} := by
  obtain ⟨⟨h1, hmul⟩, hiso, hcont⟩ := hσ
  have hemb : Topology.IsEmbedding (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Formalism.REAL.KG ε) := hemb.secondCountableTopology
  have hU : ∀ k : Formalism.REAL.KG ε, Formalism.REAL.toMK k ∈ Formalism.MainNotions.S.UJset ε := fun k => k.1.2
  let π : Formalism.REAL.KG ε →* (H →L[ℂ] H) :=
    { toFun := fun k => σ (Formalism.REAL.toMK k)
      map_one' := h1
      map_mul' := fun k l => hmul _ (hU k) _ (hU l) }
  have hd := dense_finite_vectors (Formalism.REAL.KG ε) H π (fun k x => hiso _ (hU k) x)
    (fun x => (hcont x).comp_continuous hemb.continuous hU)
  refine hd.mono ?_
  rintro v ⟨S, hS, hv, hSs⟩
  refine ⟨S, hS, hv, ?_⟩
  intro g hg x hx
  rw [← Formalism.REAL.range_toMK] at hg
  obtain ⟨k, rfl⟩ := hg
  exact hSs k x hx

end GlobalTheory.CompactRep
end
