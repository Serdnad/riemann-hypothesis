module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle126
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle090
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle092
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle120
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle121
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle127
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle055
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle070

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section
namespace GlobalTheory.ChainStepCoef

theorem om_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (g g' : GL a k)
    (Φ : Matrix b a k → ℂ) : om μ (g * g') (1 : GL b k) Φ = om μ g 1 (om μ g' 1 Φ) := by
  funext x
  have p1 := (nabs_pos' (GeneralLinearGroup.det g)).le
  have p2 := (nabs_pos' (GeneralLinearGroup.det g')).le
  have hm : ∀ u v : kˣ, nabs k (u * v) = nabs k u * nabs k v := fun u v => by simp [nabs, map_mul]
  have h1 : nabs k 1 = 1 := by simp [nabs]
  simp only [om, map_mul, hm, Real.mul_rpow p1 p2, inv_one, Units.val_one, Matrix.one_mul, Units.val_mul,
    Matrix.mul_assoc, map_one, h1, Real.one_rpow]
  push_cast
  ring

theorem om_smul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (g : GL a k)
    (h : GL b k) (c : ℂ) (Φ : Matrix b a k → ℂ) :
    om μ g h (fun x => c * Φ x) = fun x => c * om μ g h Φ x := by
  funext x
  simp only [om]
  ring

theorem ip_smul_left {k : Type} [Field k] [MeasurableSpace k] (ν : Measure k) {m n : Type} [Fintype m] [Fintype n]
    (c : ℂ) (F G : Matrix m n k → ℂ) : ip ν (fun x => c * F x) G = c * ip ν F G := by
  unfold ip
  simp_rw [mul_assoc]
  exact integral_const_mul c _

theorem ip_smul_right {k : Type} [Field k] [MeasurableSpace k] (ν : Measure k) {m n : Type} [Fintype m] [Fintype n]
    (c : ℂ) (F G : Matrix m n k → ℂ) : ip ν F (fun x => c * G x) = starRingEnd ℂ c * ip ν F G := by
  unfold ip
  simp_rw [map_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem part1 (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν)
    (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (ξ μ₀ : kˣ →* ℂˣ) (hξu : IsUnitaryChar ξ) (hξt : IsTame ξ) (hμu : IsUnram μ₀) (hμn : IsUnitaryChar μ₀) :
    IsBiType ξ (fun g : GL (A ⊕ D) k =>
      ip ν (om (μ₀ * ξ) g (1 : GL (A ⊕ E) k) (datum ξ)) (datum ξ : Matrix (A ⊕ E) (A ⊕ D) k → ℂ)) := by
  haveI := hν.1
  have hμ' : ∀ x, ‖((μ₀ * ξ) x : ℂ)‖ = 1 := fun x => by
    simp [MonoidHom.mul_apply, Units.val_mul, norm_mul, hξu x, hμn x]
  have hL1 := GlobalTheory.T.parahoricDatum_eigenvector_twoBlockParahoric k A D E ξ μ₀ hξt hμu
  intro j hj d hd g
  have hu : (ξ d : ℂ) * starRingEnd ℂ (ξ d) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hξu d]; simp
  refine ⟨?_, ?_⟩
  · have h1 := ip_om_om k _ _ ν (μ₀ * ξ) hμ' j 1 (om (μ₀ * ξ) g 1 (datum ξ : Matrix (A ⊕ E) (A ⊕ D) k → ℂ))
      (datum ξ)
    rw [← om_mul, hL1 j hj d hd, ip_smul_right] at h1
    simp only
    rw [← h1, ← mul_assoc, hu, one_mul]
  · simp only
    rw [om_mul, hL1 j hj d hd, om_smul, ip_smul_left]

theorem part2 (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] (ν : Measure k)
    (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (ξ μ : kˣ →* ℂˣ) (x : GL A k) (y : GL D k) :
    ip ν (om μ (emb₂ k (Equiv.refl (A ⊕ D)) (x, y)) (1 : GL (A ⊕ E) k) (datum ξ))
      (datum ξ : Matrix (A ⊕ E) (A ⊕ D) k → ℂ) ≠ 0 → x ∈ KO k A := by
  intro h
  by_contra hx
  apply h
  unfold ip
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.zero_apply, om, inv_one, Units.val_one, Matrix.one_mul]
  by_cases h1 : InSupp z
  · have h2 : ¬ InSupp (z * (emb₂ k (Equiv.refl (A ⊕ D)) (x, y) : Matrix (A ⊕ D) (A ⊕ D) k)) :=
      fun h2 => hx (GlobalTheory.T.mem_integralGL_of_inParahoricDatumSupport_mul_blockDiag k A D E z x y h1 h2)
    simp [datum, h2]
  · simp [datum, h1]

theorem det_mtor {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    GeneralLinearGroup.det (mtor ϖ e : GL (A ⊕ D) k) = ϖ ^ ∑ i, e i := by
  ext
  rw [GeneralLinearGroup.val_det_apply, mtor, val_torusElt, det_diagonal, Units.val_zpow_eq_zpow_val,
    Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul]
  induction (Finset.univ : Finset D) using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ (Units.ne_zero ϖ), ih]

theorem nabs_det_mtor {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) (e : D → ℤ) :
    nabs k (GeneralLinearGroup.det (mtor ϖ e : GL (A ⊕ D) k)) = (resCard k : ℝ) ^ (-∑ i, e i) := by
  rw [mtor, nabs_det_torusElt hϖ, Fintype.sum_sum_type]
  simp

theorem part3 (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν)
    (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (r : ℕ)
    (D E : Type) [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (ξ μ : kˣ →* ℂˣ) (hξu : IsUnitaryChar ξ) (e : D → ℤ) :
    ip ν (om μ (mtor ϖ e) (1 : GL (Fin r ⊕ E) k) (datum ξ)) (datum ξ : Matrix (Fin r ⊕ E) (Fin r ⊕ D) k → ℂ) =
      (μ ϖ : ℂ) ^ (∑ i, e i) * ((volAdd ν r * ((resCard k : ℝ) ^ (r * Fintype.card E))⁻¹ : ℝ) : ℂ) *
      (resCard k : ℂ) ^ (-((r + Fintype.card E : ℕ) : ℂ) / 2 * (sumAbs e : ℂ)) := by
  haveI := hν.1
  obtain ⟨hS, hV⟩ := GlobalTheory.T.measure_parahoricDatumSupport k ν hν r D E
  have q1 : 1 < Nat.card 𝓀[k] := Finite.one_lt_card
  have q0 : (0 : ℝ) < resCard k := by unfold resCard; exact_mod_cast (lt_trans one_pos q1)
  set Φ : Matrix (Fin r ⊕ E) (Fin r ⊕ D) k → ℂ := datum ξ with hΦ
  set m : GL (Fin r ⊕ D) k := mtor ϖ e with hm
  set f : D → ℤ := fun i => -max 0 (-e i) with hf
  set m' : GL (Fin r ⊕ D) k := mtor ϖ f with hm'
  set S := {x : Matrix (Fin r ⊕ E) (Fin r ⊕ D) k | InSupp x} with hSdef
  have h1 : nabs k 1 = 1 := by simp [nabs]
  have hA : ∀ x, om μ m 1 Φ x * starRingEnd ℂ (Φ x) =
      ((μ (GeneralLinearGroup.det m) : ℂ) * ((nabs k (GeneralLinearGroup.det m) ^
        ((Fintype.card (Fin r ⊕ E) : ℝ) / 2) : ℝ) : ℂ)) * (Φ (x * m.val) * starRingEnd ℂ (Φ x)) := by
    intro x
    simp only [om, inv_one, Units.val_one, Matrix.one_mul, map_one, h1, Real.one_rpow]
    push_cast
    ring
  have hB : ∀ x, Φ (x * m.val) * starRingEnd ℂ (Φ x) = S.indicator (fun _ => (1 : ℂ)) (x * m'.val) := by
    intro x
    exact GlobalTheory.T.parahoricDatum_torus_integrand_eq_indicator k ϖ hϖ (Fin r) D E ξ hξu e x
  have hC := integral_comp_mul_mul_volM ν m' (1 : GL (Fin r ⊕ E) k) (S.indicator (fun _ => (1 : ℂ)))
  simp only [Units.val_one, Matrix.one_mul, map_one, h1, Real.one_rpow, one_mul] at hC
  have hI : ∫ x, S.indicator (fun _ => (1 : ℂ)) x ∂(volM ν (Fin r ⊕ E) (Fin r ⊕ D)) =
      (volM ν (Fin r ⊕ E) (Fin r ⊕ D)).real S • (1 : ℂ) := by
    exact integral_indicator_const (μ := volM ν (Fin r ⊕ E) (Fin r ⊕ D)) (1 : ℂ) hS
  unfold ip
  simp_rw [hA, hB]
  rw [integral_const_mul, hC, hI, hV, nabs_det_mtor hϖ, nabs_det_mtor hϖ, det_mtor,
    map_zpow, Units.val_zpow_eq_zpow_val]
  have hsumZ : sumAbs e = ∑ i, e i - 2 * ∑ i, f i := by
    unfold sumAbs
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hf]
    rcases le_total 0 (e i) with h | h
    · rw [abs_of_nonneg h, max_eq_left (by omega)]; ring
    · rw [abs_of_nonpos h, max_eq_right (by omega)]; ring
  have hsum : (sumAbs e : ℝ) = ∑ i, (e i : ℝ) - 2 * ∑ i, (f i : ℝ) := by
    rw [hsumZ]; push_cast; ring
  have key : ((resCard k : ℝ) ^ (-∑ i, e i)) ^ (((r + Fintype.card E : ℕ) : ℝ) / 2) *
      ((resCard k : ℝ) ^ (-∑ i, f i)) ^ (-((r + Fintype.card E : ℕ) : ℝ)) =
      (resCard k : ℝ) ^ ((-((r + Fintype.card E : ℕ) : ℝ) / 2) * (sumAbs e : ℝ)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul q0.le, ← Real.rpow_mul q0.le,
      ← Real.rpow_add q0, hsum]
    congr 1
    push_cast
    ring
  have hc : (resCard k : ℂ) ^ (-((r + Fintype.card E : ℕ) : ℂ) / 2 * (sumAbs e : ℂ)) =
      (((resCard k : ℝ) ^ ((-((r + Fintype.card E : ℕ) : ℝ) / 2) * (sumAbs e : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow q0.le]
    push_cast
    ring_nf
  rw [hc, ← key]
  simp only [Fintype.card_sum, Fintype.card_fin, Complex.real_smul, smul_eq_mul, mul_one]
  push_cast
  ring

theorem coef : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
  ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r t l : ℕ) (ξ μ₀' : kˣ →* ℂˣ), IsUnitaryChar ξ → IsTame ξ → IsUnram μ₀' → IsUnitaryChar μ₀' →
  let μ' : kˣ →* ℂˣ := μ₀' * ξ
  let Φ : Matrix (Fin r ⊕ Blocks (l + 1) t) (Fin r ⊕ Blocks l t) k → ℂ := datum ξ
  let c : GL (Fin r ⊕ Blocks l t) k → ℂ := fun g => ip ν (om μ' g (1 : GL (Fin r ⊕ Blocks (l + 1) t) k) Φ) Φ
  IsBiType ξ c ∧
  (∀ x y, c (emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) (x, y)) ≠ 0 → x ∈ KO k (Fin r)) ∧
  ∀ e : Blocks l t → ℤ, c (mtor ϖ e) = (μ' ϖ : ℂ) ^ (∑ i, e i) *
    ((volAdd ν r * ((resCard k : ℝ) ^ (r * ((l + 1) * t)))⁻¹ : ℝ) : ℂ) *
    (resCard k : ℂ) ^ (-((r + (l + 1) * t : ℕ) : ℂ) / 2 * (sumAbs e : ℂ)) := by
  intro k _ _ _ _ _ _ ν hν ϖ hϖ r t l ξ μ₀' hξu hξt hμu hμn μ' Φ c
  have hE : Fintype.card (Blocks (l + 1) t) = (l + 1) * t := by simp [Blocks]
  refine ⟨part1 k ν hν (Fin r) (Blocks l t) (Blocks (l + 1) t) ξ μ₀' hξu hξt hμu hμn,
    fun x y => part2 k ν (Fin r) (Blocks l t) (Blocks (l + 1) t) ξ (μ₀' * ξ) x y, fun e => ?_⟩
  have := part3 k ν hν ϖ hϖ r (Blocks l t) (Blocks (l + 1) t) ξ (μ₀' * ξ) hξu e
  rw [hE] at this
  exact this

end GlobalTheory.ChainStepCoef
end
end

section

noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

namespace GlobalTheory.SmGL.Exponents

theorem leviChar_unit_injective {R β : Type} [CommRing R] [Fintype β] {χ ψ : β → Rˣ →* ℂˣ}
    (h : leviChar (fun _ : β => Unit) χ = leviChar (fun _ : β => Unit) ψ) : χ = ψ := by
  classical
  funext j
  ext1 x
  have key : ∀ φ : β → Rˣ →* ℂˣ, leviChar (fun _ : β => Unit) φ
      (Pi.mulSingle j (Matrix.GeneralLinearGroup.scalar Unit x)) = φ j x := by
    intro φ
    rw [leviChar_apply, Finset.prod_eq_single j]
    · rw [Pi.mulSingle_eq_same]
      congr 1
      ext
      simp
    · intro b _ hb
      rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one]
    · simp
  rw [← key χ, ← key ψ, h]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmoothChar_leviChar_of_smooth {β : Type} [Fintype β] (c : β → Type) [∀ j, Fintype (c j)]
    [∀ j, DecidableEq (c j)] {χ : β → kˣ →* ℂˣ} (h : ∀ j, IsSmoothChar (χ j)) :
    IsSmoothChar (leviChar c χ) := by
  unfold leviChar
  refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) isSmoothChar_one
    fun a _ => ?_
  exact (h a).detChar.comp _ (continuous_apply a)

theorem nonempty_cell_term_equiv {α β : Type} [Fintype α] [LinearOrder α] [Fintype β]
    {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    (g : ∀ j, (Σ i, c i j) ≃ Unit) (s : ∀ i j, IrrRep (GL (c i j) k)) (ψ : α → β → kˣ →* ℂˣ)
    (hψ : ∀ i j, IsSmoothChar (ψ i j)) (e : ∀ i j, Nonempty ((s i j).ρ.Equiv (detRep (c i j) (ψ i j)))) :
    Nonempty ((piTensor fun j => multiProd (g j) fun i => (s i j).ρ).Equiv
      (ofChar (leviChar (fun _ : β => Unit) fun j => ψ ((g j).symm ()).1 j))) := by
  obtain ⟨a⟩ := nonempty_piTensor_detRep_equiv k β (fun _ => Unit) fun j => ψ ((g j).symm ()).1 j
  refine ⟨Representation.Equiv.trans (LocGL.piTensorEquiv fun j => ?_) a⟩
  exact (LocGL.multiProdEquiv (g j) fun i => (e i j).some).trans
    (GlobalTheory.T.parabolicInduction_detCharacters_rank_one_equiv k α (fun i => c i j) (g j) (fun i => ψ i j) (fun i => hψ i j)).some

theorem jhMult_leviChar_cellFunctor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], CellSemisimplification k → ∀ (α β : Type) [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ Unit) (X : α → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] (ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)), (∀ i, IsSmooth (ρ i)) → (∀ i, HasFiniteLength (ρ i)) → ∀ χ : β → kˣ →* ℂˣ, (∀ j, IsSmoothChar (χ j)) → jhMult (ofChar (leviChar (fun _ : β => Unit) χ)) (cellFunctor (m' := fun _ : β => Unit) f g (piTensor ρ)) = ∏ i, jhMult (ofChar (leviChar (c i) χ)) (jac (f i) (ρ i)) := by
  intro k _ _ _ _ hC α β _ _ _ _ m _ _ c _ _ f g X _ _ ρ hρ hl χ hχ
  obtain ⟨T, hT0, hT⟩ := hC α β m (fun _ => Unit) c f g X ρ hρ hl
  have h1 := hT (IrrRep.ofChar (leviChar (fun _ : β => Unit) χ) (isSmoothChar_leviChar_of_smooth _ hχ))
  refine Eq.trans h1 ?_
  let s₀ : ∀ i j, IrrCl (GL (c i j) k) := fun i j => (IrrRep.det (c i j) (χ j) (hχ j)).cl
  have e₀ : ∀ i j, Nonempty ((s₀ i j).rep.ρ.Equiv (detRep (c i j) (χ j))) := fun i j =>
    (IrrRep.det (c i j) (χ j) (hχ j)).nonempty_equiv_rep
  have hfac : ∀ i, jhMult (piTensor fun j => (s₀ i j).rep.ρ) (jac (f i) (ρ i)) =
      jhMult (ofChar (leviChar (c i) χ)) (jac (f i) (ρ i)) := fun i =>
    jhMult_congr_left ((LocGL.piTensorEquiv fun j => (e₀ i j).some).trans
      (nonempty_piTensor_detRep_equiv k β (c i) χ).some) _
  rw [Finset.sum_eq_single s₀]
  · obtain ⟨a⟩ := nonempty_cell_term_equiv g (fun i j => (s₀ i j).rep) (fun _ j => χ j)
      (fun _ j => hχ j) e₀
    have h2 : jhMult (ofChar (leviChar (fun _ : β => Unit) χ))
        (piTensor fun j => multiProd (g j) fun i => (s₀ i j).rep.ρ) = 1 :=
      (jhMult_congr_right _ a).trans (jhMult_self (isIrreducible_ofChar _))
    exact (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => hfac i) h2).trans (mul_one _)
  · intro s _ hs
    have hsub : ∀ i j, Subsingleton (c i j) := fun i j =>
      ⟨fun x y => sigma_mk_injective (β := fun i => c i j) ((g j).injective (Subsingleton.elim _ _))⟩
    choose ψ hψ e using fun i j =>
      GlobalTheory.T.exists_equiv_detCharacter_of_irreducible_rank_le_one k (c i j) _ (s i j).rep.ρ (s i j).rep.smooth (s i j).rep.irr
    obtain ⟨a⟩ := nonempty_cell_term_equiv g (fun i j => (s i j).rep) ψ hψ e
    refine mul_eq_zero_of_right _ ((jhMult_congr_right _ a).trans (Model.jhMult_ofChar_ne fun h => hs ?_))
    have h3 := leviChar_unit_injective h
    funext i j
    have h4 : detChar (c i j) (ψ i j) = detChar (c i j) (χ j) := by
      rcases isEmpty_or_nonempty (c i j) with hc | ⟨⟨x⟩⟩
      · ext1 y
        rw [detChar_apply, detChar_apply, show Matrix.GeneralLinearGroup.det y = 1 from
          Units.ext (by simp), map_one, map_one]
      · have : (g j).symm () = ⟨i, x⟩ := (g j).injective (Subsingleton.elim _ _)
        rw [congrFun h3 j, this]
    rw [← (s i j).cl_rep]
    refine IrrRep.cl_eq_iff.2 ⟨(e i j).some.trans ?_⟩
    show (ofChar (detChar (c i j) (ψ i j))).Equiv (ofChar (detChar (c i j) (χ j)))
    rw [h4]
    exact .refl _
  · intro hs
    obtain ⟨i, hi⟩ := hT0 s₀ hs
    exact mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ i) hi) _

end GlobalTheory.SmGL.Exponents
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.ProdSupport

theorem piTensor_mulSingle {α : Type} [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (a : α) (g : Γ a) (c : ℂ) (h : ∀ v, ρ a g v = c • v) (y : ⨂[ℂ] a, X a) :
    piTensor ρ (Pi.mulSingle a g) y = c • y := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, smul_comm, piTensor_tprod]
    congr 1
    have h1 : (fun b => ρ b (Pi.mulSingle (M := Γ) a g b) (x b)) = Function.update x a (c • x a) := by
      funext b
      by_cases hb : b = a
      · subst hb
        simp [h]
      · simp [Pi.mulSingle_eq_of_ne hb, Function.update_of_ne hb]
    rw [h1, MultilinearMap.map_update_smul, Function.update_eq_self]
    simp

theorem nontrivial_piTensor {α : Type} [Fintype α] (X : α → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (h : ∀ a, Nontrivial (X a)) : Nontrivial (⨂[ℂ] a, X a) := by
  have h1 : ∀ a, ∃ (x : X a) (l : Module.Dual ℂ (X a)), l x = 1 := fun a => by
    obtain ⟨x, hx⟩ := exists_ne (0 : X a)
    obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hx
    exact ⟨x, l, hl⟩
  choose x l hl using h1
  refine ⟨PiTensorProduct.tprod ℂ x, 0, fun h0 => ?_⟩
  have := congrArg
    (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap l)) h0
  simp [hl] at this

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_scalar_one {d : ℕ} (hd : d = 1) (z : kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin d) z) = z := by
  ext; simp [GeneralLinearGroup.scalar, hd]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem eq_scalar_det {d : ℕ} (hd : d = 1) (g : GL (Fin d) k) :
    g = GeneralLinearGroup.scalar (Fin d) (GeneralLinearGroup.det g) := by
  subst hd
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp [GeneralLinearGroup.scalar, GeneralLinearGroup.val_det_apply]

theorem hasCentralChar_multiProd {α n : Type} [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n]
    {c : α → Type} [∀ a, Fintype (c a)] [∀ a, DecidableEq (c a)] (e : (Σ a, c a) ≃ n)
    {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (c a) k) (X a)) (a : α) (ha : ∀ b, b ≠ a → IsEmpty (c b))
    {ω : kˣ →* ℂˣ} (hω : HasCentralChar (σ a) ω) : HasCentralChar (multiProd e σ) ω := by
  intro z f
  have h1 : leviEmb k e (Pi.mulSingle a (GeneralLinearGroup.scalar (c a) z)) =
      GeneralLinearGroup.scalar n z := by
    ext i j
    obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b', y'⟩, rfl⟩ := e.surjective j
    obtain rfl : b = a := by_contra fun h => (ha b h).elim y
    obtain rfl : b' = b := by_contra fun h => (ha b' h).elim y'
    rw [leviEmb_apply_same]
    simp [GeneralLinearGroup.scalar, diagonal_apply]
  have h2 : modExp c a = 0 := by
    unfold modExp
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
    · intro b hb
      have := ha b (Finset.mem_filter.1 hb).2.ne
      simp
    · intro b hb
      have := ha b (Finset.mem_filter.1 hb).2.ne'
      simp
  have h3 : deltaHalf k c (Pi.mulSingle a (GeneralLinearGroup.scalar (c a) z)) = 1 := by
    rw [deltaHalf_apply]
    refine Finset.prod_eq_one fun b _ => ?_
    by_cases hb : b = a
    · subst hb
      simp [h2]
    · rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one]
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  have h4 := parInd_law e (piTensor σ) f
    ⟨_, leviEmb_mem_parab k e (Pi.mulSingle a (GeneralLinearGroup.scalar (c a) z))⟩ x
  rw [leviProj_leviEmb, h3, piTensor_mulSingle σ a _ _ (hω z)] at h4
  have hc : x * GeneralLinearGroup.scalar n z = GeneralLinearGroup.scalar n z * x := by
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  show f.1.1 (x * GeneralLinearGroup.scalar n z) = (ω z : ℂ) • f.1.1 x
  rw [hc, ← h1]
  simpa using h4

theorem exists_inSupport_of_multiProd : GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α]
    (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (n : Type) [Fintype n] [DecidableEq n]
    (e : (Σ a, m a) ≃ n) (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (χ : kˣ →* ℂˣ),
    (∀ a, IsSmooth (ρ a)) → (∀ a, (ρ a).IsIrreducible) → InSupport (multiProd e ρ) χ →
      ∃ a, InSupport (ρ a) χ := by
  intro hG k _ _ _ _ α _ _ m _ _ n _ _ e X _ _ ρ χ hs hi
  rintro ⟨r, d, e', a, ha, Y, _, _, τ, hτ, hsub, hact⟩
  obtain ⟨b, f, g, s, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2 e e' hs
    (fun i => hasFiniteLength_of_isIrreducible (hi i)) hτ hsub
  have hsum : ∑ i, b.1 i a = 1 := by simpa [ha] using b.2.2 a
  obtain ⟨i, -, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.trans_ne one_ne_zero)
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => b.1 j a) (Finset.mem_univ i)
  have hi1 : b.1 i a = 1 := by simp only at hsplit; omega
  have hz : ∀ j, j ≠ i → IsEmpty (Fin (b.1 j a)) := fun j hj => by
    have h0 : ∑ j ∈ Finset.univ.erase i, b.1 j a = 0 := by simp only at hsplit; omega
    rw [Finset.sum_eq_zero_iff.1 h0 j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)]
    infer_instance
  obtain ⟨ω, -, hω⟩ := LocGL.exists_smooth_hasCentralChar (s i a).smooth (s i a).irr
  have hcen := hasCentralChar_multiProd (g a) (fun j => (s j a).ρ) i hz hω
  obtain rfl : χ = ω := by
    have := Model.nontrivial_of_isIrreducible hτ
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    refine MonoidHom.ext fun z => ?_
    have h1 := Model.scalar_of_isSubquotient hcol
      (piTensor_mulSingle (fun j => multiProd (g j) fun i => (s i j).ρ) a _ _ (hcen z)) y
    rw [hact, det_scalar_one ha] at h1
    exact Units.ext (smul_left_injective ℂ hy h1)
  obtain ⟨Z, _, _, υ, hυ, hυs⟩ := IrrSubquot.exists_irreducible_subquotient _ _
    (piTensor fun j => (s i j).ρ)
    (nontrivial_piTensor _ fun j => Model.nontrivial_of_isIrreducible (s i j).irr)
  refine ⟨i, r, b.1 i, f i, a, hi1, Z, _, _, υ, hυ, hυs.trans (hrow i), fun h y => ?_⟩
  refine Model.scalar_of_isSubquotient hυs (piTensor_mulSingle (fun j => (s i j).ρ) a h _ fun v => ?_) y
  conv_lhs => rw [eq_scalar_det hi1 h]
  exact hω _ v

end GlobalTheory.ProdSupport
end
end
