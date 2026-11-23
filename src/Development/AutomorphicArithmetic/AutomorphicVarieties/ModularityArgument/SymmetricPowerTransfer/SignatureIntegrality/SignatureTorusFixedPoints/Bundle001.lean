module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryHyperbolicOrbitCount
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.Bundle001
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.LevelTwoFiniteIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenVal

@[expose] public section

section

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem UpperTheory.V.Z.Sym.Sig.isOpen_Kc (c : ℕ) : IsOpen (Kc k n c : Set (GL (Fin n) k)) := by
  have ho : IsOpen {x : k | valuation k x ≤ uniformizer k ^ (c : ℤ)} := by
    have h0 : IsOpen ((valuation k).integer : Set k) := Valuation.isOpen_integer
    convert h0.preimage (continuous_mul_const ((unif k ^ (-(c : ℤ)) : kˣ) : k)) using 1
    ext x
    change _ ↔ valuation k _ ≤ 1
    rw [map_mul, GlAx.val_zpow, _root_.zpow_neg, mul_inv_le_iff₀ (zpow_pos GlAx.unif_pos _), one_mul]
    rfl
  have h : ∀ f : GL (Fin n) k → GL (Fin n) k, Continuous f → IsOpen {g | GlAx.Bd c (f g)} := fun f hf => by
    simp only [GlAx.Bd, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      ho.preimage (((Units.continuous_val.comp hf).sub continuous_const).matrix_elem i j)
  have : (Kc k n c : Set (GL (Fin n) k)) = {g | GlAx.Bd c (id g)} ∩ {g | GlAx.Bd c g⁻¹} := Set.ext fun g => GlAx.mem_Kc
  rw [this]
  exact (h _ continuous_id).inter (h _ continuous_inv)

theorem UpperTheory.V.Z.Sym.Sig.kc_sep {g : GL (Fin n) k} (h : ∀ m, g ∈ Kc k n m) : g = 1 := by
  refine Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => ?_))
  by_contra h0
  have := (GlAx.mem_Kc.1 (h ((ord k (Units.mk0 _ h0)).natAbs + 1))).1 i j
  rw [show (g.val - 1) i j = (Units.mk0 _ h0 : kˣ) from rfl, val_ord,
    zpow_le_zpow_iff_right_of_lt_one₀ GlAx.unif_pos uniformizer_lt_one] at this
  omega

theorem UpperTheory.V.Z.Sym.Sig.kc_basis {S : Set (GL (Fin n) k)} (hS : S ∈ nhds (1 : GL (Fin n) k)) : ∃ m, (Kc k n m : Set (GL (Fin n) k)) ⊆ S := by
  by_contra hc
  push_neg at hc
  have hcl : ∀ m, IsClosed ((Kc k n m : Set (GL (Fin n) k)) \ interior S) := fun m =>
    ((Kc k n m).isClosed_of_isOpen (isOpen_Kc m)).sdiff isOpen_interior
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (fun m => (Kc k n m : Set (GL (Fin n) k)) \ interior S)
    (fun m _ h => ⟨GlAx.Kc_anti (Nat.le_succ m) h.1, h.2⟩)
    (fun m => by obtain ⟨x, h1, h2⟩ := Set.not_subset.1 (hc m); exact ⟨x, h1, fun h => h2 (interior_subset h)⟩)
    (GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (hcl 0) fun _ h => GlAx.Kc_le 0 h.1) hcl
  have h1 : a = 1 := kc_sep fun m => (Set.mem_iInter.1 ha m).1
  exact (Set.mem_iInter.1 ha 0).2 (h1 ▸ mem_interior_iff_mem_nhds.2 hS)

end

theorem UpperTheory.V.Z.Sym.Sig.fixPt : UpperTheory.V.Z.Sym.Sig.FixPt := by
  intro k _ _ _ _ n Q hQ Ψ hΨ
  have hle : Q ≤ KO k (Fin n) := by
    rcases hQ with rfl | ⟨c, rfl⟩
    exacts [fun _ h => h.2, fun _ h => GlAx.Kc_le _ h.2]
  have ce : ∀ i j, Continuous fun g : GL (Fin n) k => g.val i j := fun i j => Units.continuous_val.matrix_elem i j
  have hcl : IsClosed (Q : Set (GL (Fin n) k)) := by
    rcases hQ with rfl | ⟨c, rfl⟩
    · have : (((glIwa k n).N : Subgroup _) : Set (GL (Fin n) k)) =
          ((⋂ i, ⋂ j, ⋂ (_ : j < i), {g | g.val i j = 0}) ∩ ⋂ i, {g | g.val i i = 1}) ∩ KO k (Fin n) := by
        ext g
        simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
        exact and_congr_left' (mem_unipB _)
      rw [this]
      exact ((isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (ce i j) continuous_const).inter
        (isClosed_iInter fun i => isClosed_eq (ce i i) continuous_const)).inter ((KO k (Fin n)).isClosed_of_isOpen GlobalTheory.SplitFlip.isOpen_KO)
    · have : (((glIwa k n).Nm c : Subgroup _) : Set (GL (Fin n) k)) =
          ((⋂ i, ⋂ j, ⋂ (_ : i < j), {g | g.val i j = 0}) ∩ ⋂ i, {g | g.val i i = 1}) ∩ Kc k n (c + 1) := by
        ext g
        simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
        exact and_congr_left' GlAx.mem_low
      rw [this]
      exact ((isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (ce i j) continuous_const).inter
        (isClosed_iInter fun i => isClosed_eq (ce i i) continuous_const)).inter ((Kc k n _).isClosed_of_isOpen (isOpen_Kc _))
  have hc : IsCompact (Q : Set (GL (Fin n) k)) := GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset hcl hle
  haveI : CompactSpace Q := isCompact_iff_compactSpace.1 hc
  have hcont : Continuous Ψ := by
    refine continuous_iff_continuousAt.2 fun a => ?_
    rw [ContinuousAt, Filter.tendsto_def]
    intro S hS
    obtain ⟨m, hm⟩ := kc_basis (S := (fun g : GL (Fin n) k => (Ψ a : GL (Fin n) k) * g) ⁻¹' {g | ∀ h : g ∈ Q, (⟨g, h⟩ : Q) ∈ S}) (by
      refine (continuous_const_mul _).continuousAt.preimage_mem_nhds ?_
      rw [mul_one]
      obtain ⟨W, hW, hW'⟩ := (mem_nhds_subtype _ _ _).1 hS
      exact Filter.mem_of_superset hW fun g hg h => hW' hg)
    have ho : IsOpen {b : Q | (a : GL (Fin n) k)⁻¹ * b ∈ Kc k n m} :=
      (isOpen_Kc m).preimage (continuous_const.mul continuous_subtype_val)
    refine Filter.mem_of_superset (ho.mem_nhds (by simp)) fun b hb => ?_
    have := hm (GlAx.Kc_anti (Nat.le_succ m) (hΨ m a b hb))
    simp only [Set.mem_preimage, mul_inv_cancel_left, Set.mem_setOf_eq] at this
    exact this (Ψ b).2
  let C : ℕ → Set Q := fun m => {a | (a : GL (Fin n) k)⁻¹ * Ψ a ∈ Kc k n m}
  have hne : ∀ m, (C m).Nonempty := fun m => by
    induction m with
    | zero => exact ⟨1, by
        show _ ∈ Kc k n 0
        rw [GlAx.Kc_zero]; exact mul_mem (inv_mem (hle (1 : Q).2)) (hle (Ψ 1).2)⟩
    | succ m ih => obtain ⟨a, ha⟩ := ih; exact ⟨Ψ a, hΨ m _ _ ha⟩
  have hC : ∀ m, IsClosed (C m) := fun m => ((Kc k n m).isClosed_of_isOpen (isOpen_Kc m)).preimage
    (continuous_subtype_val.inv.mul (continuous_subtype_val.comp hcont))
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
    (fun m _ h => GlAx.Kc_anti (Nat.le_succ m) h) hne (hC 0).isCompact hC
  refine ⟨a, Subtype.ext (inv_mul_eq_one.1 (kc_sep fun m => Set.mem_iInter.1 ha m)).symm⟩

end
end

section

open Matrix Polynomial GlobalTheory.SplitWeil GlobalTheory.SmGL

private theorem exists_eigvec {k : Type} [Field k] (M : Matrix (Fin 2) (Fin 2) k) (c : k)
    (h : M.charpoly.eval c = 0) : ∃ v : Fin 2 → k, v ≠ 0 ∧ M *ᵥ v = c • v := by
  rw [Matrix.eval_charpoly] at h
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec] at hMv
  have hs : Matrix.scalar (Fin 2) c *ᵥ v = c • v := by
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_smul]
  rw [hs] at hMv
  exact (sub_eq_zero.mp hMv).symm

theorem UpperTheory.V.Z.Sym.Sig.normalD :
    UpperTheory.V.Z.Sym.Sig.NormalD := by
  intro k _ _ _ _ γ a b hab hchar
  have ha : (γ : Matrix (Fin 2) (Fin 2) k).charpoly.eval (a : k) = 0 := by
    simp [hchar]
  have hb : (γ : Matrix (Fin 2) (Fin 2) k).charpoly.eval (b : k) = 0 := by
    simp [hchar]
  obtain ⟨v, hv0, hv⟩ := exists_eigvec _ _ ha
  obtain ⟨w, hw0, hw⟩ := exists_eigvec _ _ hb
  have hab' : (a : k) ≠ (b : k) := fun h => hab (Units.ext h)
  let P : Matrix (Fin 2) (Fin 2) k := Matrix.of fun i j => ![v, w] j i
  have hPv : ∀ u : Fin 2 → k, P *ᵥ u = u 0 • v + u 1 • w := by
    intro u
    ext i
    simp [P, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  have hdet : P.det ≠ 0 := by
    intro h0
    obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [hPv] at hu
    have h2 : (γ : Matrix (Fin 2) (Fin 2) k) *ᵥ (u 0 • v + u 1 • w) = 0 := by
      rw [hu, Matrix.mulVec_zero]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hv, hw] at h2
    have h3 : (u 1 * ((b : k) - a)) • w = 0 := by
      have e : (u 1 * ((b : k) - a)) • w
          = (u 0 • (a : k) • v + u 1 • (b : k) • w) - (a : k) • (u 0 • v + u 1 • w) := by
        module
      rw [e, h2, hu, smul_zero, sub_zero]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · have hu1 : u 1 = 0 := by
        rcases mul_eq_zero.mp h4 with h5 | h5
        · exact h5
        · exact absurd (sub_eq_zero.mp h5).symm hab'
      rw [hu1, zero_smul, add_zero] at hu
      rcases smul_eq_zero.mp hu with h6 | h6
      · apply hu0
        ext i
        fin_cases i
        · simpa using h6
        · simpa using hu1
      · exact hv0 h6
    · exact hw0 h4
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P hdet, ?_⟩
  have hg : ((Matrix.GeneralLinearGroup.mkOfDetNeZero P hdet : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = P := rfl
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  simp only [Units.val_mul, hg, UpperTheory.V.Z.Sym.Sig.dg, val_diagT]
  ext i j
  fin_cases j
  · have := congrFun hv i
    simp [Matrix.mulVec, dotProduct] at this
    simp [P, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]
    rw [this, mul_comm]
  · have := congrFun hw i
    simp [Matrix.mulVec, dotProduct] at this
    simp [P, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]
    rw [this, mul_comm]
end

section

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Sig.conjDiag : UpperTheory.V.Z.Sym.Sig.ConjDiag := by
  intro k _ _ _ _ n s s' hs hs' y hy
  have hc : (dg s : GL (Fin n) k) * y = y * dg s' := by
    rw [← hy, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  have hM := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k)) hc
  simp only [Units.val_mul, UpperTheory.V.Z.Sym.Sig.dg, val_diagT] at hM
  have key : ∀ i j, (y : Matrix (Fin n) (Fin n) k) i j ≠ 0 → (s i : k) = s' j := by
    intro i j hij
    have e := congrFun (congrFun hM i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm] at e
    exact mul_left_cancel₀ hij e
  have hdet : (y : Matrix (Fin n) (Fin n) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero
  have col : ∀ j, ∃ i, (y : Matrix (Fin n) (Fin n) k) i j ≠ 0 := by
    intro j
    by_contra h
    push_neg at h
    exact hdet (Matrix.det_eq_zero_of_column_eq_zero j h)
  choose σ hσ using col
  have hσs : ∀ j, (s (σ j) : k) = s' j := fun j => key _ _ (hσ j)
  have hmono : StrictMono σ := by
    intro j j' hjj'
    have h1 := hs' j j' hjj'
    rw [← hσs, ← hσs] at h1
    by_contra hle
    push_neg at hle
    rcases hle.lt_or_eq with h2 | h2
    · exact lt_irrefl _ (lt_trans h1 (hs _ _ h2))
    · rw [h2] at h1
      exact lt_irrefl _ h1
  have hid : σ = id := hmono.eq_id
  have hss : ∀ j, (s j : k) = s' j := by
    intro j
    have := hσs j
    rwa [hid] at this
  have inj : ∀ i j, (s i : k) = s j → i = j := by
    intro i j h
    rcases lt_trichotomy i j with hij | hij | hij
    · have := hs i j hij
      rw [h] at this
      exact absurd this (lt_irrefl _)
    · exact hij
    · have := hs j i hij
      rw [h] at this
      exact absurd this (lt_irrefl _)
  have hdiag : ∀ i j, i ≠ j → (y : Matrix (Fin n) (Fin n) k) i j = 0 := by
    intro i j hij
    by_contra h
    exact hij (inj i j ((key i j h).trans (hss j).symm))
  have hne : ∀ i, (y : Matrix (Fin n) (Fin n) k) i i ≠ 0 := by
    intro i
    have := hσ i
    rwa [hid] at this
  refine ⟨funext fun j => Units.ext (hss j), fun i => Units.mk0 _ (hne i), ?_⟩
  apply Units.ext
  simp only [UpperTheory.V.Z.Sym.Sig.dg, val_diagT, Units.val_mk0]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [hdiag i j hij, Matrix.diagonal_apply_ne _ hij]

end
end

section

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem vo {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : kˣ) :
    valuation k (x : k) = uniformizer k ^ ord k x := by
  have h1 := GlAx.val_div_ord x
  have h2 := GlAx.val_zpow (k := k) (ord k x)
  have e : (x : k) = ((x / unif k ^ ord k x : kˣ) : k) * ((unif k ^ ord k x : kˣ) : k) := by
    rw [← Units.val_mul, div_mul_cancel]
  rw [e, map_mul, h1, h2, one_mul]

theorem UpperTheory.V.Z.Sym.Sig.shrink : UpperTheory.V.Z.Sym.Sig.Shrink := by
  intro k _ _ _ _ n d hd m
  set a : Fin n → ℤ := fun i => ord k (d i) with ha
  have hv : ∀ i, valuation k (d i : k) = uniformizer k ^ a i := fun i => vo (d i)
  have hlt : ∀ i j : Fin n, i < j → a j < a i := by
    intro i j hij
    have h := hd i j hij
    rw [hv, hv] at h
    exact (zpow_right_strictAnti₀ GlAx.unif_pos ValuativeRel.uniformizer_lt_one).lt_iff_gt.1 h
  have hanti : Antitone a := by
    intro i j hij
    rcases hij.lt_or_eq with h | h
    · exact (hlt i j h).le
    · rw [h]
  have hv' : ∀ i, valuation k ((d⁻¹) i : k) = uniformizer k ^ (-a i) := by
    intro i
    rw [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hv, _root_.zpow_neg]
  refine ⟨fun x hx hxm => ?_, fun c y hy hym => ?_⟩
  · have hx' : x ∈ unipB k (Fin n) ⊓ KO k (Fin n) := hx
    refine Subgroup.mem_inf.2 ⟨GlAx.conj_N hv hanti hx, ?_⟩
    rw [GlAx.mem_Kc] at hxm ⊢
    refine GlAx.conj_Kc (c' := ((m + 1 : ℕ) : ℤ)) (Subgroup.mem_inf.1 hx').1 hxm d a hv ?_
    intro i j
    rcases le_or_gt j i with h | h
    · exact Or.inl fun z hz => GlAx.up_sub_one hz h
    · right
      have := hlt i j h
      push_cast
      omega
  · have hy' : y ∈ Subgroup.comap (GlobalTheory.CuspRep.invT n k) (unipB k (Fin n)) ⊓ Kc k n (c + 1) := hy
    have e1 : (dg d)⁻¹ = diagT k (Fin n) d⁻¹ := (map_inv _ _).symm
    have e2 : dg d = (diagT k (Fin n) d⁻¹)⁻¹ := by
      rw [← map_inv, inv_inv]
    rw [e1, e2]
    refine Subgroup.mem_inf.2 ⟨GlAx.conj_Nm (a := fun i => -a i) hv' (c := c) (c' := c) ?_ hy, ?_⟩
    · intro i j h
      have := hlt j i h
      omega
    · rw [GlAx.mem_Kc] at hym ⊢
      refine GlAx.conj_Kc (c' := ((m + 1 : ℕ) : ℤ)) (Subgroup.mem_inf.1 hy').1 hym d⁻¹
        (fun i => -a i) hv' ?_
      intro i j
      rcases le_or_gt i j with h | h
      · exact Or.inl fun z hz => GlAx.low_sub_one hz h
      · right
        have := hlt j i h
        push_cast
        omega

end
end

section

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Sig.factJ : UpperTheory.V.Z.Sym.Sig.FactJ := by
  intro k _ _ _ _ V n
  constructor
  · have hm : ∀ {a b : GL (Fin n) k}, (∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, a = x * t * y) →
        (∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, b = x * t * y) →
        ∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, a * b = x * t * y := by
      rintro _ _ ⟨x, hx, t, ht, y, hy, rfl⟩ ⟨x', hx', t', ht', y', hy', rfl⟩
      obtain ⟨x2, hx2, s, hs, y2, hy2, h⟩ := (glIwa k n).swap V.c y hy x' hx'
      refine ⟨x * (t * x2 * t⁻¹), mul_mem hx ((glIwa k n).T_N t (V.levelTorus_le_torus ht) x2 hx2), t * s * t',
        mul_mem (mul_mem ht (V.Tc_le_TH hs)) ht', (t'⁻¹ * y2 * t'⁻¹⁻¹) * y',
        mul_mem ((glIwa k n).T_Nm V.c t'⁻¹ (inv_mem (V.levelTorus_le_torus ht')) y2 hy2) hy', ?_⟩
      calc x * t * y * (x' * t' * y') = x * t * (y * x') * t' * y' := by group
        _ = _ := by rw [h]; group
    have h1 : ∀ a ∈ (glIwa k n).N, ∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, a = x * t * y :=
      fun a ha => ⟨a, ha, 1, one_mem _, 1, one_mem _, by simp⟩
    have h2 : ∀ a ∈ V.TH n, ∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, a = x * t * y :=
      fun a ha => ⟨1, one_mem _, a, ha, 1, one_mem _, by simp⟩
    have h3 : ∀ a ∈ (glIwa k n).Nm V.c, ∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, a = x * t * y :=
      fun a ha => ⟨1, one_mem _, 1, one_mem _, a, ha, by simp⟩
    let K : Subgroup (GL (Fin n) k) :=
      { carrier := {g | ∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, g = x * t * y}
        mul_mem' := hm
        one_mem' := h1 1 (one_mem _)
        inv_mem' := by
          rintro _ ⟨x, hx, t, ht, y, hy, rfl⟩
          have := hm (h3 _ (inv_mem hy)) (hm (h2 _ (inv_mem ht)) (h1 _ (inv_mem hx)))
          simpa only [_root_.mul_inv_rev, Set.mem_setOf_eq] using this }
    exact fun g hg => (show V.J n ≤ K from sup_le (sup_le h1 h2) h3) hg
  · rintro m a ha a' ha' _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ b hb b' hb' h
    have hT : ∀ s : Fin n → kˣ, (∀ i, s i ∈ V.H) → dg s ∈ KO k (Fin n) := fun s h => V.J_le_KO (V.dg_mem h)
    have k1 := Kc_conj (mul_mem (hT s' fun i => hs' i trivial) (V.J_le_KO (V.Nm_le hb'))) h
    set κ := dg s' * b' * ((a * diagT k (Fin n) s * b)⁻¹ * (a' * diagT k (Fin n) s' * b')) * (dg s' * b')⁻¹ with hκ
    set l := dg s * (b * b'⁻¹) * (dg s')⁻¹ with hl
    have e : a⁻¹ * a' = l * κ := by
      have : l * κ = dg s * b * ((a * diagT k (Fin n) s * b)⁻¹ * (a' * diagT k (Fin n) s' * b')) * (dg s' * b')⁻¹ := by
        rw [hl, hκ]; group
      rw [this]; group
    have hl0 : l ∈ KO k (Fin n) := mul_mem (mul_mem (hT s fun i => hs i trivial) (V.J_le_KO (V.Nm_le (mul_mem hb (inv_mem hb')))))
      (inv_mem (hT s' fun i => hs' i trivial))
    have hl1 : ∀ i j, i < j → (l : Matrix (Fin n) (Fin n) k) i j = 0 := fun i j hij => by
      rw [hl, dg, dg, ← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, mul_diagonal, diagonal_mul,
        (GlAx.mem_low.1 (mul_mem hb (inv_mem hb')).1).1 i j hij]
      simp
    have hu := mul_mem (inv_mem ha) ha'
    refine mem_Kc_of hu.2 fun i j => ?_
    rcases le_or_gt j i with hij | hij
    · rw [GlAx.up_sub_one hu.1 hij]; simp
    · have e2 : ((a⁻¹ * a').val - 1) i j = ∑ r, l.val i r * (κ.val - 1) r j := by
        rw [← Matrix.mul_apply, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, Matrix.sub_apply, hl1 i j hij, one_apply_ne hij.ne, e,
          Units.val_mul]
      rw [e2]
      refine Valuation.map_sum_le _ fun r _ => ?_
      rw [map_mul]
      exact (mul_le_mul' (GlAx.bd_zero.1 (GlAx.mem_KO.1 hl0).1 i r) ((GlAx.mem_Kc.1 k1).1 r j)).trans_eq (one_mul _)

end
end
