module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle007
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundUniformiser
import Formalism.PolynomialDimension.MultinomialDepth.PartnerM
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle006
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle008
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle003
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

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

section Lvl

variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem Ljj_span_fd (j : Fin G.T.t → ℕ) (jp : ℕ) :
    FiniteDimensional ℚ_[p] (Submodule.span ℚ_[p] (Ljj p (r := r) G j jp : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]))) := by
  classical
  set Yq := Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr with hYq
  haveI : FiniteDimensional ℚ_[p] (Formalism.GM.M.Pol p r (G.lettersAt j jp)) := Formalism.CountingSumsFrames.pol_finiteDimensional _
  haveI : FiniteDimensional ℚ_[p] Yq := Submodule.finiteDimensional_of_le inf_le_left
  let bY := Module.finBasis ℚ_[p] Yq
  let Ms := xiMons (r := r) G (G.B - jp)
  let fam : Fin (Module.finrank ℚ_[p] Yq) × Ms → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] :=
    fun ab => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY ab.1 : Yq) : _) * monomial (ab.2 : _ →₀ ℕ) 1
  let W := Submodule.span ℚ_[p] (Set.range fam)
  have hle : Ljj p (r := r) G j jp ≤ W.restrictScalars ℤ_[p] := by
    unfold Ljj
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, g, hg, rfl⟩
    have hyY : y ∈ Yq := (Submodule.mem_inf.1 hy).1
    have hy2 : y ∈ Submodule.span ℚ_[p] (Set.range fun a => ((bY a : Yq) : MvPolynomial _ ℚ_[p])) := by
      have h3 : (⟨y, hyY⟩ : Yq) ∈ (⊤ : Submodule ℚ_[p] Yq) := Submodule.mem_top
      rw [← bY.span_eq] at h3
      have h4 := Submodule.mem_map_of_mem (f := Yq.subtype) h3
      rw [Submodule.map_span, ← Set.range_comp] at h4
      exact h4
    have hg2 := xi_mem_span p G (G.B - jp) g hg
    show rename (Formalism.GM.M.chainEmb N r G.T.t) y * g ∈ W
    have hy3 : rename (Formalism.GM.M.chainEmb N r G.T.t) y ∈ Submodule.span ℚ_[p]
        (Set.range fun a => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY a : Yq) : MvPolynomial _ ℚ_[p])) := by
      have := Submodule.mem_map_of_mem (f := (rename (Formalism.GM.M.chainEmb N r G.T.t) :
        MvPolynomial _ ℚ_[p] →ₐ[ℚ_[p]] MvPolynomial _ ℚ_[p]).toLinearMap) hy2
      rw [Submodule.map_span, ← Set.range_comp] at this
      exact this
    have hmul := Submodule.mul_mem_mul hy3 hg2
    rw [Submodule.span_mul_span] at hmul
    refine Submodule.span_mono ?_ hmul
    rintro _ ⟨u, ⟨a, rfl⟩, v, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨(a, ⟨m, hm⟩), rfl⟩
  haveI : FiniteDimensional ℚ_[p] W := FiniteDimensional.span_of_finite ℚ_[p] (Set.finite_range fam)
  have hle2 : Submodule.span ℚ_[p] (Ljj p (r := r) G j jp : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])) ≤ W := by
    rw [Submodule.span_le]
    intro x hx
    exact hle hx
  exact Submodule.finiteDimensional_of_le hle2

theorem finrank_Ljj_span (j : Fin G.T.t → ℕ) (jp : ℕ) :
    Module.finrank ℤ_[p] (Ljj p (r := r) G j jp) =
      Module.finrank ℚ_[p] (Submodule.span ℚ_[p] (Ljj p (r := r) G j jp : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]))) :=
  finrank_eq_span_gen (R := ℤ_[p]) (K := ℚ_[p]) _

end Lvl

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

def RestPlusAW (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) : Prop :=
  Formalism.GM.M.goodCount p (fun F F' => Formalism.GM.M.fockN p (G.lettersAt j jp) (G.T.phis p (r := r) (G.lettersAt j jp) F) F')
            (Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr) D * dXi r (G.B - jp) ≤
    Formalism.GM.M.goodCount p (bePhi p (r := r) G j jp) (Ljj p (r := r) G j jp) D

theorem plusA_of (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) (h : RestPlusAW p (r := r) G j jp D) :
    Formalism.GM.M.bad p (bePhi p (r := r) G j jp) (Ljj p (r := r) G j jp) D ≤ badY p (r := r) G j jp D * dXi r (G.B - jp) := by
  have h1 := finrank_Ljj_le p (r := r) G j jp
  have hY : Module.finrank ℤ_[p] (Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr) = dimY p (r := r) G j jp :=
    Formalism.CountingSumsFrames.finrank_lattice _ _ inf_le_left
  unfold badY
  simp only [Formalism.GM.M.bad]
  rw [hY, Nat.sub_mul]
  unfold RestPlusAW at h
  omega

end Level

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestPlusAWI (CM : ℝ) : Prop :=
  ∀ dl ∈ CountingStatementReduction.clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    RestPlusAW X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 ⌊D1r C0 CE1 CE2 X CM⌋

theorem restPlusA_of (CM : ℝ) (h : RestPlusAWI C0 CE1 CE2 X CM) : RestPlusA C0 CE1 CE2 X CM := by
  intro dl hdl aTop ha x hx
  exact plusA_of X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 _ (h dl hdl aTop ha x hx)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem restDimBC_proved : RestDimBC C0 CE1 CE2 X := by
  intro aTop _ aPlus _ b _
  set Dd := blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b with hDd
  set V0 := Submodule.span ℚ_[X.p]
    (((gmB Dd).SSZ X.p (r := X.r) : Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) :
      Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) with hV0
  set W := Submodule.span (KK X.O) ((Dd.SSZ X.O (r := X.r) : Submodule X.O (MvPolynomial (BVar (2 * X.s + 1) X.r Dd.T.t) (KK X.O))) :
      Set (MvPolynomial (BVar (2 * X.s + 1) X.r Dd.T.t) (KK X.O))) with hW
  show Module.finrank ℚ_[X.p] V0 ≤ Module.finrank (KK X.O) W
  have : FiniteDimensional (KK X.O) W := span_SSZ_finite Dd
  by_cases hfin : FiniteDimensional ℚ_[X.p] V0
  swap
  · rw [Module.finrank_of_not_finite hfin]
    exact Nat.zero_le _

  have hmemW : ∀ x ∈ V0, MvPolynomial.map (iotaX X) x ∈ W := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact map_SSZ (ι := iotaX X) (iotaX_int X) Dd x hx
    | zero => rw [map_zero]; exact W.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact W.add_mem hx hy
    | smul a x _ hx => rw [map_smul_Q]; exact W.smul_mem _ hx
  set bs := Module.finBasis ℚ_[X.p] V0
  have hli : LinearIndependent ℚ_[X.p] (fun i => (bs i : MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) :=
    bs.linearIndependent.map' V0.subtype (Submodule.ker_subtype V0)
  have hli2 := li_map (iotaX X) _ hli
  let w : Fin (Module.finrank ℚ_[X.p] V0) → W := fun i => ⟨MvPolynomial.map (iotaX X) (bs i).1, hmemW _ (bs i).2⟩
  have hli3 : LinearIndependent (KK X.O) w := LinearIndependent.of_comp W.subtype hli2
  have h := hli3.fintype_card_le_finrank
  rw [Fintype.card_fin] at h
  exact h

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Chain

variable {s : ℕ} {p r : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (b : SegBlock s r)

theorem segChain_deg_even (x : Fin (2 * s + 1)) (u : Fin s) (hx : (x : ℕ) = 2 * (u : ℕ)) (hu : S.sigma ≤ (u : ℕ)) :
    (segChain p S aTop b).deg x = b.o u := by
  have hu' := u.isLt
  have hne : (x : ℕ) ≠ 2 * s := by omega
  have ht : topOf x hne = u := Fin.ext (by simp [topOf]; omega)
  simp only [segChain]
  rw [dite_eq_right hne, if_pos (by omega), ht, if_neg (by omega)]

theorem segChain_deg_odd (x : Fin (2 * s + 1)) (u : Fin s) (hx : (x : ℕ) = 2 * (u : ℕ) + 1)
    (hu : S.sigma ≤ (u : ℕ)) : (segChain p S aTop b).deg x = coarseC p S aTop b u := by
  have hu' := u.isLt
  have hne : (x : ℕ) ≠ 2 * s := by omega
  have ht : topOf x hne = u := Fin.ext (by simp [topOf]; omega)
  simp only [segChain]
  rw [dite_eq_right hne, if_neg (by omega), ht, if_neg (by omega)]

theorem segChain_deg_last (x : Fin (2 * s + 1)) (hx : (x : ℕ) = 2 * s) : (segChain p S aTop b).deg x = b.oPlus := by
  simp only [segChain]
  rw [dite_eq_left hx]

end Chain

theorem mem_levels_iff {N : ℕ} (G : Formalism.GM.M.BlockData N) (x : (Fin G.T.t → ℕ) × ℕ) :
    x ∈ levels G ↔ G.LevelOK x.1 x.2 := by
  simp only [levels, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [Finset.mem_product, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, ?_⟩
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      exact (h.1 i).1.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      exact h.2.trans (min_le_right _ _)

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

theorem uTop_ge (i : Fin (X.S C0 CE1 CE2).t) : (X.S C0 CE1 CE2).sigma ≤ ((uTop (X.S C0 CE1 CE2) i : Fin X.s) : ℕ) := by
  simp only [uTop]
  omega

theorem levelOK_gB (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) :
    (gB C0 CE1 CE2 X aTop aPlus b).LevelOK x.1 x.2 ↔
      (∀ i : Fin (X.S C0 CE1 CE2).t, x.1 i ≤ b.o (uTop (X.S C0 CE1 CE2) i) ∧
        x.1 i ≤ coarseC X.p (X.S C0 CE1 CE2) aTop b (uTop (X.S C0 CE1 CE2) i)) ∧
      x.2 ≤ min b.oPlus (X.S C0 CE1 CE2).bPlus := by
  simp only [Formalism.GM.M.BlockData.LevelOK, gB, gmB, blockData, BlockData.withMargin, blockBase, gmL, gmT, segTies]
  refine and_congr (forall_congr' fun i => ?_) ?_
  · have hi := (uTop (X.S C0 CE1 CE2) i).isLt
    rw [segChain_deg_even (X.S C0 CE1 CE2) aTop b
        ⟨min (2 * ((uTop (X.S C0 CE1 CE2) i : Fin X.s) : ℕ)) (2 * X.s + 1 - 1), by omega⟩ (uTop _ i)
        (by simp only; omega) (uTop_ge i),
      segChain_deg_odd (X.S C0 CE1 CE2) aTop b
        ⟨min (2 * ((uTop (X.S C0 CE1 CE2) i : Fin X.s) : ℕ) + 1) (2 * X.s + 1 - 1), by omega⟩ (uTop _ i)
        (by simp only; omega) (uTop_ge i)]
  · rw [segChain_deg_last (X.S C0 CE1 CE2) aTop b ⟨2 * X.s, by omega⟩ rfl]

theorem mem_lv (aTop : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) :
    x ∈ lv C0 CE1 CE2 X aTop b ↔
      (∀ i : Fin (X.S C0 CE1 CE2).t, x.1 i ≤ b.o (uTop (X.S C0 CE1 CE2) i) ∧
        x.1 i ≤ coarseC X.p (X.S C0 CE1 CE2) aTop b (uTop (X.S C0 CE1 CE2) i)) ∧
      x.2 ≤ min b.oPlus (X.S C0 CE1 CE2).bPlus :=
  (mem_levels_iff (gB C0 CE1 CE2 X aTop 0 b) x).trans (levelOK_gB aTop 0 b x)

theorem digitsOK_of_compat {dl : DCl X} {aTop : Fin X.s → ℕ} (hc : Compat C0 CE1 CE2 X dl aTop)
    (b : SegBlock X.s X.r) (hb : (b.rz, b.ry) = dl) : DigitsOK X.p (X.S C0 CE1 CE2) aTop b := by
  subst hb
  simpa only [Compat, DigitsOK, ColumnSystems.digitBlock] using hc

theorem mem_cbox' {dl : DCl X} {aTop : Fin X.s → ℕ} (ha : aTop ∈ cbox C0 CE1 CE2 X dl) :
    aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA) ∧ Compat C0 CE1 CE2 X dl aTop := by
  simp only [cbox, Finset.mem_filter] at ha
  exact ha

theorem idx_sub (hS : SegFacts C0 CE1 CE2 X) (dl : DCl X) (aTop aTop' : Fin X.s → ℕ)
    (ha : aTop ∈ cbox C0 CE1 CE2 X dl) (ha' : aTop' ∈ cbox C0 CE1 CE2 X dl) :
    idx C0 CE1 CE2 X dl aTop ⊆ idx C0 CE1 CE2 X dl aTop' := by
  haveI : NeZero X.r := ⟨X.hm⟩
  have hF := hS.hF
  have hwin : ∀ i, X.L.a ≤ aTop' i := fun i =>
    (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (mem_cbox' ha').1 i)).1
  have hp : (25:ℝ) ≤ X.L.p := by
    have h1 := hF.p_ge
    have h2 : (4:ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
    nlinarith
  have hb0 := hF.b0
  have hblt := hF.b_lt
  have h25 : 25 * X.L.b' < X.L.a := by nlinarith
  rintro ⟨b, x⟩ hbx
  simp only [idx, Finset.mem_sigma, Finset.mem_filter] at hbx ⊢
  obtain ⟨⟨hk, hdl⟩, hx⟩ := hbx
  rw [mem_keptSet] at hk ⊢
  have hD' := digitsOK_of_compat (mem_cbox' ha').2 b hdl
  have hsum : ∀ i, ((∑ c, b.ry i c : ℕ) : ℝ) < X.L.b' := by
    intro i
    have h1 : ∑ c, b.ry i c < ∑ _c : Fin (X.r + 1), SegData.P X.p (X.S C0 CE1 CE2) i :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun c _ => (hD'.1 i c).2)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    have h2 := hS.kP i
    have h3 : ((∑ c, b.ry i c : ℕ) : ℝ) < (((X.r + 1) * SegData.P X.p (X.S C0 CE1 CE2) i : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h3 ⊢
    linarith
  have hC : ∀ i, (coarseC X.p (X.S C0 CE1 CE2) aTop' b i : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) =
      (aTop' i : ℝ) - ((∑ c, b.ry i c : ℕ) : ℝ) := by
    intro i
    have h1 := Nat.div_mul_cancel (hD'.2.2 i).2
    have h2 := (hD'.2.2 i).1
    unfold coarseC
    rw [← Nat.cast_sub h2, ← Nat.cast_mul, h1]
  have hAC : ∀ i, coarseA X.p (X.S C0 CE1 CE2) b i ≤ coarseC X.p (X.S C0 CE1 CE2) aTop' b i := by
    intro i
    have h1 := hS.bTop i
    have h2 := hsum i
    have h3 : (X.L.a : ℝ) ≤ aTop' i := by exact_mod_cast hwin i
    have h4 : (((X.S C0 CE1 CE2).bTop i + ∑ c, b.ry i c : ℕ) : ℝ) < aTop' i := by
      push_cast at h2 ⊢
      linarith
    have h5 : (X.S C0 CE1 CE2).bTop i + ∑ c, b.ry i c < aTop' i := by exact_mod_cast h4
    unfold coarseA coarseC
    exact Nat.div_le_div_right (by omega)
  have hSG : ∀ i, ((b.sg i : ℕ) : ℝ) ≤ 2 * (X.S C0 CE1 CE2).La *
      ((SegData.A0 X.p (X.S C0 CE1 CE2) : ℤ) : ℝ) / ((X.r : ℝ) + 1) →
      b.sg i ≤ coarseC X.p (X.S C0 CE1 CE2) aTop' b i := by
    intro i h
    have hP1 : (1:ℝ) ≤ (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) := by exact_mod_cast hS.P1 i
    have hPQ : (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) ≤ (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) := by
      exact_mod_cast hS.PQ i
    have hQ : (0:ℝ) < (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) := by linarith
    have hA : ((SegData.A0 X.p (X.S C0 CE1 CE2) : ℤ) : ℝ) ≤ (X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) := by
      have h1 := Int.floor_le ((((X.S C0 CE1 CE2).a : ℝ) - (X.S C0 CE1 CE2).E0) /
        (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ))
      have h2 := hS.E0
      have h3 : (((X.S C0 CE1 CE2).a : ℝ) - (X.S C0 CE1 CE2).E0) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) ≤
          (X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) := by
        apply div_le_div_of_nonneg_right _ hQ.le
        show (X.L.a : ℝ) - (X.S C0 CE1 CE2).E0 ≤ X.L.a
        linarith
      exact h1.trans h3
    have hLa0 : 0 ≤ (X.S C0 CE1 CE2).La := hF.La0
    have hLa4 : 4 * (X.S C0 CE1 CE2).La < (X.r : ℝ) + 1 := hS.La4
    have hr : (0:ℝ) < (X.r : ℝ) + 1 := by positivity
    have hq0 : 0 ≤ (X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) := by positivity
    have e1 : 2 * (X.S C0 CE1 CE2).La * ((SegData.A0 X.p (X.S C0 CE1 CE2) : ℤ) : ℝ) / ((X.r : ℝ) + 1) ≤
        2 * (X.S C0 CE1 CE2).La * ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / ((X.r : ℝ) + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by linarith)) hr.le
    have e2 : 2 * (X.S C0 CE1 CE2).La * ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / ((X.r : ℝ) + 1) ≤
        ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / 2 := by
      rw [div_le_div_iff₀ hr (by norm_num)]
      nlinarith
    have e3 : ((b.sg i : ℕ) : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) ≤ (X.L.a : ℝ) / 2 := by
      have h0 : ((b.sg i : ℕ) : ℝ) ≤ ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / 2 :=
        h.trans (e1.trans e2)
      calc ((b.sg i : ℕ) : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)
          ≤ ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / 2 * (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) :=
            mul_le_mul h0 hPQ (by linarith) (by positivity)
        _ = (X.L.a : ℝ) / 2 := by field_simp
    have e4 : (X.L.a : ℝ) - X.L.b' < (aTop' i : ℝ) - ((∑ c, b.ry i c : ℕ) : ℝ) := by
      have h1 := hsum i
      have h2 : (X.L.a : ℝ) ≤ aTop' i := by exact_mod_cast hwin i
      linarith
    have e5 : ((b.sg i : ℕ) : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) <
        (coarseC X.p (X.S C0 CE1 CE2) aTop' b i : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) := by
      rw [hC i]
      linarith
    have e6 : ((b.sg i : ℕ) : ℝ) < (coarseC X.p (X.S C0 CE1 CE2) aTop' b i : ℝ) :=
      lt_of_mul_lt_mul_right e5 (by linarith)
    exact_mod_cast e6.le
  refine ⟨⟨⟨hD', hk.2.1, fun i hi => ?_, hk.2.2.2⟩, hdl⟩, ?_⟩
  · obtain ⟨h1, h2, _, h4, h5⟩ := hk.2.2.1 i hi
    exact ⟨h1, h2, hSG i h5, h4, h5⟩
  · have hx' := (mem_lv aTop b x).mp hx
    refine (mem_lv aTop' b x).mpr ⟨fun i => ⟨(hx'.1 i).1, ?_⟩, hx'.2⟩
    exact (hx'.1 i).1.trans (((hk.2.1 _ (uTop_ge i)).1).trans (hAC _))

theorem restFree_proved (hS : SegFacts C0 CE1 CE2 X) : RestFree C0 CE1 CE2 X := fun dl _ aTop ha aTop' ha' =>
  Finset.Subset.antisymm (idx_sub hS dl aTop aTop' ha ha') (idx_sub hS dl aTop' aTop ha' ha)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
