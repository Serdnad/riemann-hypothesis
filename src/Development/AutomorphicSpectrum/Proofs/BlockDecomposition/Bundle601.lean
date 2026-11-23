module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle596
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeValuesSameParameters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Formalism.SatakeDualWeyl.Bundle001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle592
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle593
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle588
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle594
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFive
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS.SatConv

theorem esymm_cons_succ' (a : ℂ) (s : Multiset ℂ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.sum_map_mul_left]

theorem coeff_prod_one_add (s : Multiset ℂ) (n : ℕ) :
    ((s.map fun a => (1 + Polynomial.C a * Polynomial.X : Polynomial ℂ)).prod).coeff n = s.esymm n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, Polynomial.coeff_add,
      Polynomial.coeff_C_mul]
    cases n with
    | zero => simp [ih, Multiset.esymm]
    | succ n => rw [Polynomial.coeff_X_mul, ih, ih, esymm_cons_succ']

theorem esymm_add_antidiagonal (s t : Multiset ℂ) (k : ℕ) :
    (s + t).esymm k = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, s.esymm p.1 * t.esymm p.2 := by
  rw [← coeff_prod_one_add, Multiset.map_add (f := _), Multiset.prod_add, Polynomial.coeff_mul]
  simp only [coeff_prod_one_add]

theorem esymm_map_mul_unit (B : Multiset ℂˣ) (z : ℂˣ) (j : ℕ) :
    ((B.map (· * z)).map fun b : ℂˣ => (b : ℂ)).esymm j =
      (z : ℂ) ^ j * (B.map fun b : ℂˣ => (b : ℂ)).esymm j := by
  have h := Multiset.pow_smul_esymm (z : ℂ) j (B.map fun b : ℂˣ => (b : ℂ))
  simp only [smul_eq_mul, Multiset.map_map, Function.comp_def] at h
  simp only [Multiset.map_map, Function.comp_def, Units.val_mul, mul_comm _ (z : ℂ)]
  exact h.symm

theorem esymm_eq_zero_of_card_lt (s : Multiset ℂ) {k : ℕ} (h : s.card < k) : s.esymm k = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_eq_empty k h]

theorem satEig_join : ∀ (q n a b : ℕ) (c : ℂˣ) (Ba Bb : Multiset ℂˣ), q ≠ 0 → a + b = n → Ba.card = a → Bb.card = b → ∀ k ≤ n, satEig q n (Ba.map (· * c ^ b) + Bb.map (· * c ^ a)) k = ∑ p ∈ pairs a b k, coef q c a b p.1 p.2 * (satEig q a Ba p.1 * satEig q b Bb p.2) := by
  intro q n a b c Ba Bb hq hab hBa hBb k _
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  subst hab
  rw [pairs, Finset.sum_filter]
  simp only [satEig]
  rw [Multiset.map_add (f := _), esymm_add_antidiagonal, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨i, j⟩ hp
  have hk : i + j = k := by simpa using hp
  subst hk
  simp only [esymm_map_mul_unit]
  split_ifs with h
  · have hpow : (q : ℂ) ^ ((((i + j : ℕ) : ℂ) * (((a + b : ℕ) : ℂ) - ((i + j : ℕ) : ℂ))) / 2) =
        (q : ℂ) ^ (((i : ℂ) * b + (j : ℂ) * a) / 2 - (i : ℂ) * j) *
          ((q : ℂ) ^ (((i : ℂ) * ((a : ℂ) - i)) / 2) * (q : ℂ) ^ (((j : ℂ) * ((b : ℂ) - j)) / 2)) := by
      rw [← Complex.cpow_add _ _ hq', ← Complex.cpow_add _ _ hq']
      congr 1
      push_cast
      ring
    rw [hpow, coef]
    simp only [Units.val_pow_eq_pow_val]
    rw [pow_add, pow_mul, pow_mul, pow_right_comm (c : ℂ) i b, pow_right_comm (c : ℂ) j a]
    ring
  · have hz : (Ba.map fun x : ℂˣ => (x : ℂ)).esymm i = 0 ∨ (Bb.map fun x : ℂˣ => (x : ℂ)).esymm j = 0 := by
      by_cases hi : i ≤ a
      · right
        refine esymm_eq_zero_of_card_lt _ ?_
        rw [Multiset.card_map, hBb]
        by_contra hj
        exact h ⟨hi, by omega⟩
      · left
        refine esymm_eq_zero_of_card_lt _ ?_
        rw [Multiset.card_map, hBa]
        omega
    rcases hz with hz | hz <;> simp [hz]

end GlobalTheory.CompanionTheory.CtS.SatConv
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS.TjChar

open GlobalTheory.WeylGL (tor tor_val tor_add tor_const_comm IntM intM_tor intM_doset)

theorem sum_ite_lt (n m : ℕ) : ∑ j : Fin n, (if (j : ℕ) < m then (1 : ℤ) else 0) = min (n : ℤ) m := by
  rw [Finset.sum_boole, Fin.card_filter_val_lt]
  push_cast
  rfl

theorem antitone_eq {n k : ℕ} {a : Fin n → ℤ} (ha : Antitone a) (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1)
    (hs : ∑ i, a i = (k : ℤ)) (i : Fin n) : a i = if (i : ℕ) < k then 1 else 0 := by
  have hi := i.2
  have hc : a i = 0 ∨ a i = 1 := by
    have := h0 i
    have := h1 i
    omega
  rcases hc with hc | hc
  · have hle : ∑ j, a j ≤ ∑ j : Fin n, (if (j : ℕ) < (i : ℕ) then (1 : ℤ) else 0) := by
      refine Finset.sum_le_sum fun j _ => ?_
      split_ifs with hj
      · exact h1 j
      · have : a j ≤ a i := ha (Fin.le_def.2 (by omega))
        omega
    rw [hs, sum_ite_lt] at hle
    have : k ≤ (i : ℕ) := by omega
    rw [hc, if_neg (by omega)]
  · have hle : ∑ j : Fin n, (if (j : ℕ) < (i : ℕ) + 1 then (1 : ℤ) else 0) ≤ ∑ j, a j := by
      refine Finset.sum_le_sum fun j _ => ?_
      split_ifs with hj
      · have : a i ≤ a j := ha (Fin.le_def.2 (by omega))
        omega
      · exact h0 j
    rw [hs, sum_ite_lt] at hle
    have : (i : ℕ) < k := by
      push_cast at hle
      omega
    rw [hc, if_pos this]

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {ϖ : w.adicCompletion E}

theorem ordL_eq_of_v {x : w.adicCompletion E} {m : ℤ} (h : Valued.v x = WithZero.exp (-m)) : ordL x = m := by
  have hx : Valued.v x ≠ 0 := by
    rw [h]
    exact WithZero.exp_ne_zero
  have e : WithZero.unzero hx = Multiplicative.ofAdd (-m) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h]
    rfl
  unfold ordL
  rw [dite_eq_right hx, e]
  simp

theorem v_zpow_eq (hu : IsUnifV E w ϖ) (m : ℤ) : Valued.v (ϖ ^ m) = WithZero.exp (-m) := by
  rw [map_zpow₀, hu]
  have : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1) := rfl
  rw [this, ← WithZero.exp_zsmul]
  simp

theorem v_prod_zpow (hu : IsUnifV E w ϖ) (a : Fin n → ℤ) (s : Finset (Fin n)) :
    Valued.v (∏ i ∈ s, ϖ ^ a i) = WithZero.exp (-∑ i ∈ s, a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, map_mul, ih, v_zpow_eq hu, ← WithZero.exp_add]
    congr 1
    ring

theorem ordL_det (h0 : ϖ ≠ 0) (hu : IsUnifV E w ϖ) {c d : GL (Fin n) (w.adicCompletion E)}
    (hc : c ∈ GLint (Fin n) (Ov E w)) (hd : d ∈ GLint (Fin n) (Ov E w)) (a : Fin n → ℤ) :
    ordL (c * tor h0 a * d : GL (Fin n) (w.adicCompletion E)).val.det = ∑ i, a i := by
  apply ordL_eq_of_v
  have h1 : Valued.v c.val.det = 1 := GlobalTheory.SphGal.isUnitAt_det_of_mem hc
  have h2 : Valued.v d.val.det = 1 := GlobalTheory.SphGal.isUnitAt_det_of_mem hd
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, h1, h2, tor_val,
    Matrix.det_diagonal, v_prod_zpow hu]
  simp

theorem tor_inv (h0 : ϖ ≠ 0) (a : Fin n → ℤ) : (tor h0 a)⁻¹ = tor h0 (-a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← tor_add]
  ext1
  simp [tor_val]

theorem tor_one_val (h0 : ϖ ≠ 0) (x : GL (Fin n) (w.adicCompletion E)) :
    (tor h0 (fun _ => 1) * x : GL (Fin n) (w.adicCompletion E)).val = ϖ • x.val := by
  ext i j
  simp [tor_val, Matrix.diagonal_mul]

theorem intM_iff {c d x y : GL (Fin n) (w.adicCompletion E)} (hc : c ∈ GLint (Fin n) (Ov E w))
    (hd : d ∈ GLint (Fin n) (Ov E w)) (e : x = c * y * d) : IntM x ↔ IntM y :=
  ⟨fun h => intM_doset h ⟨c⁻¹, Subgroup.inv_mem _ hc, d⁻¹, Subgroup.inv_mem _ hd, by rw [e]; group⟩,
    fun h => intM_doset h ⟨c, hc, d, hd, e⟩⟩

theorem isInt_iff (h0 : ϖ ≠ 0) (hu : IsUnifV E w ϖ) {c d : GL (Fin n) (w.adicCompletion E)}
    (hc : c ∈ GLint (Fin n) (Ov E w)) (hd : d ∈ GLint (Fin n) (Ov E w)) (a : Fin n → ℤ) :
    IsInt w (c * tor h0 a * d : GL (Fin n) (w.adicCompletion E)).val ↔ ∀ i, 0 ≤ a i :=
  (intM_iff hc hd rfl).trans (intM_tor h0 hu a)

theorem isInt_dual_iff (h0 : ϖ ≠ 0) (hu : IsUnifV E w ϖ) {c d : GL (Fin n) (w.adicCompletion E)}
    (hc : c ∈ GLint (Fin n) (Ov E w)) (hd : d ∈ GLint (Fin n) (Ov E w)) (a : Fin n → ℤ) :
    IsInt w (ϖ • ((c * tor h0 a * d : GL (Fin n) (w.adicCompletion E))⁻¹).val) ↔ ∀ i, a i ≤ 1 := by
  rw [← tor_one_val h0]
  have e : tor h0 (fun _ => 1) * (c * tor h0 a * d)⁻¹ = d⁻¹ * tor h0 ((fun _ => 1) + -a) * c⁻¹ := by
    rw [tor_add, _root_.mul_inv_rev, _root_.mul_inv_rev, tor_inv, ← mul_assoc (tor h0 fun _ => 1) d⁻¹, tor_const_comm]
    group
  have h := (intM_iff (Subgroup.inv_mem _ hd) (Subgroup.inv_mem _ hc) e).trans (intM_tor h0 hu _)
  refine h.trans (forall_congr' fun i => ?_)
  simp

end GlobalTheory.CompanionTheory.CtS.TjChar

namespace GlobalTheory.CompanionTheory.CtS


open GlobalTheory.CompanionTheory.CtS.TjChar in
theorem Tj_eq_ite : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n k : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → k ≤ n → ∀ g : GL (Fin n) (w.adicCompletion E), Tj ℂ n (Ov E w) ϖ k g = if IsInt w g.val ∧ IsInt w (ϖ • (g⁻¹).val) ∧ ordL g.val.det = (k : ℤ) then 1 else 0 := by
  intro E _ _ w n k ϖ hu hk g
  have h0 : ϖ ≠ 0 := fun h => by simp [IsUnifV, h] at hu
  rw [GlobalTheory.WeylGL.Tj_eq h0 k]
  split_ifs with h
  · obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨a, ha, c, hc, d, hd, rfl⟩ := GlobalTheory.WeylGL.cartan h0 hu g
    have ha0 := (isInt_iff h0 hu hc hd a).1 h1
    have ha1 := (isInt_dual_iff h0 hu hc hd a).1 h2
    rw [ordL_det h0 hu hc hd] at h3
    have e : a = fun i : Fin n => if (i : ℕ) < k then 1 else 0 :=
      funext (antitone_eq ha ha0 ha1 h3)
    subst e
    exact GlobalTheory.WeylGL.dosetInd_of_mem ⟨c, hc, d, hd, rfl⟩
  · refine GlobalTheory.WeylGL.dosetInd_of_not ?_
    rintro ⟨c, hc, d, hd, rfl⟩
    refine h ⟨(isInt_iff h0 hu hc hd _).2 fun i => ?_, (isInt_dual_iff h0 hu hc hd _).2 fun i => ?_, ?_⟩
    · split_ifs <;> omega
    · split_ifs <;> omega
    · rw [ordL_det h0 hu hc hd, sum_ite_lt, min_eq_right (by exact_mod_cast hk)]

end GlobalTheory.CompanionTheory.CtS
end
end

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS

theorem det_mem_Ov {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    {M : Matrix (Fin n) (Fin n) (w.adicCompletion E)} (hM : IsInt w M) : M.det ∈ Ov E w := by
  have hN : M = (Ov E w).subtype.mapMatrix (Matrix.of fun i j => (⟨M i j, hM i j⟩ : Ov E w)) := by
    ext i j; rfl
  rw [hN, ← RingHom.map_det]
  exact SetLike.coe_mem _

private theorem v_eq_ofAdd_lemma {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
    (x : w.adicCompletion E) (hx : x ≠ 0) :
    Valued.v x = ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  rw [ordL, dite_eq_right h, neg_neg, ofAdd_toAdd, WithZero.coe_unzero]

theorem ordL_det_range : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ g : GL (Fin n) (w.adicCompletion E), IsInt w g.val → IsInt w (ϖ • (g⁻¹).val) → ∃ i ≤ n, ordL g.val.det = (i : ℤ) := by
  intro E _ _ w n ϖ hϖ g hg hgi
  have hd : g.val.det ∈ Ov E w := det_mem_Ov hg
  have hdi : (ϖ • (g⁻¹).val).det ∈ Ov E w := det_mem_Ov hgi
  have hmul : g.val.det * (g⁻¹).val.det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  have hd0 : g.val.det ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have hdi0 : (g⁻¹).val.det ≠ 0 := right_ne_zero_of_mul_eq_one hmul
  rw [Matrix.det_smul, Fintype.card_fin] at hdi
  simp only [Ov, ValuationSubring.mem_toSubring, HeightOneSpectrum.mem_adicCompletionIntegers] at hd hdi
  rw [map_mul, map_pow, show Valued.v ϖ =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from hϖ,
    v_eq_ofAdd_lemma _ hdi0, ← WithZero.coe_pow, ← WithZero.coe_mul, ← ofAdd_nsmul, ← ofAdd_add,
    ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le,
    nsmul_eq_mul, mul_neg, mul_one] at hdi
  rw [v_eq_ofAdd_lemma _ hd0, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero,
    Multiplicative.ofAdd_le] at hd
  have hm := congrArg Valued.v hmul
  rw [map_mul, map_one, v_eq_ofAdd_lemma _ hd0, v_eq_ofAdd_lemma _ hdi0, ← WithZero.coe_mul, ← ofAdd_add,
    ← WithZero.coe_one, WithZero.coe_inj, ofAdd_eq_one] at hm
  refine ⟨(ordL g.val.det).toNat, ?_, ?_⟩
  · omega
  · omega

end GlobalTheory.CompanionTheory.CtS
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.joined_projection_formula : JnPi := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.jnPi_holds | exact GlobalTheory.CompanionTheory.ColumnSplitting.jnPi_holds | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.jnPi_holds <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orbit_measure_unitary_group_invariant : QK → Law → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (h : GA D B), (nuT hn I μ x₀).map (fun z => (mm (mt B h) z.1, mm (mt B h) z.2)) = nuT hn I μ x₀ := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.InvU.nuT_map_ac | exact GlobalTheory.CompanionTheory.ColumnSplitting.InvU.nuT_map_ac | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.InvU.nuT_map_ac <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finite_on_compacts_orbit_measure : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → IsFiniteMeasureOnCompacts (nuT hn I μ x₀) := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.isFiniteMeasureOnCompacts_nuT | exact GlobalTheory.CompanionTheory.ColumnSplitting.isFiniteMeasureOnCompacts_nuT | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.isFiniteMeasureOnCompacts_nuT <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

noncomputable section

namespace GlobalTheory.CompanionTheory.NormCongr

theorem mem_norms_locPhi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ (m : (w.adicCompletion E)[X]) (c : GL (Fin n) (w.adicCompletion E)), c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) = (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val → (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m = cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val → ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m → x ∈ norms Q (v.adicCompletion (maximalRealSubfield E)) := by
  intro E _ _ _ hU w hw v hv n γ₀ hell H₀ _ hdet hinv m c hc1 hc2 r Q hQ x hx
  exact mem_norms_of_congr_equiv hU w hw (v.adicCompletion (maximalRealSubfield E)) (locJ hU w hw v hv)
    (locJ_algebraMap hU w hw v hv) (locJ_cj hU w hw v hv) n γ₀ hell H₀ hdet hinv m c hc1 hc2 r Q hQ x hx

end GlobalTheory.CompanionTheory.NormCongr
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

theorem _root_.GlobalTheory.T.local_hermitian_class_second : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ m : (w.adicCompletion E)[X], IsHerm (cj w) ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m) → ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m).det ≠ 0 → ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∃ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m := by
  first | exact @GlobalTheory.CompanionTheory.LocPhiUnit.locPhi_mem_units_plus | exact GlobalTheory.CompanionTheory.LocPhiUnit.locPhi_mem_units_plus | (intros; apply GlobalTheory.CompanionTheory.LocPhiUnit.locPhi_mem_units_plus <;> assumption)
end

section


theorem _root_.GlobalTheory.T.unramified_quadratic_condition_one : PositivityTheory.SiegelWeilFormula.Gunr.Q1 := by
  first | exact @GlobalTheory.CompanionTheory.ResidueInvolution.q1 | exact GlobalTheory.CompanionTheory.ResidueInvolution.q1 | (intros; apply GlobalTheory.CompanionTheory.ResidueInvolution.q1 <;> assumption)
end

section


theorem _root_.GlobalTheory.T.unramified_quadratic_condition_three : PositivityTheory.SiegelWeilFormula.Gunr.Q3 := by
  first | exact @GlobalTheory.CompanionTheory.GunrResCard.q3 | exact GlobalTheory.CompanionTheory.GunrResCard.q3 | (intros; apply GlobalTheory.CompanionTheory.GunrResCard.q3 <;> assumption)
end

section


theorem _root_.GlobalTheory.T.unramified_quadratic_condition_two : PositivityTheory.SiegelWeilFormula.Gunr.Q2 := by
  first | exact @GlobalTheory.CompanionTheory.ValuationCompleteness.q2 | exact GlobalTheory.CompanionTheory.ValuationCompleteness.q2 | (intros; apply GlobalTheory.CompanionTheory.ValuationCompleteness.q2 <;> assumption)
end

section


theorem _root_.GlobalTheory.T.unramified_quadratic_condition_five : PositivityTheory.SiegelWeilFormula.Gunr.Q5 := by
  first | exact @GlobalTheory.CompanionTheory.GunrInert.isField_tensor_iff_isField_quot | exact GlobalTheory.CompanionTheory.GunrInert.isField_tensor_iff_isField_quot | (intros; apply GlobalTheory.CompanionTheory.GunrInert.isField_tensor_iff_isField_quot <;> assumption)
end
