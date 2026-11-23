module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle006
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle010
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle007
public import Formalism.MahlerMeasure.MahlerMeasureProofs.SSDirect
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle011
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle009
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ExponentMatrixFirstDepthEq
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

private theorem finrank_span_blockData_gens {p : ℕ} [Fact (Nat.Prime p)] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ι : ℚ_[p] →+* KK O) {N r : ℕ} [NeZero r] (hY : RestYbc)
    (D : BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) :
    Module.finrank (KK O) (Submodule.span (KK O) (BlockData.gens (r := r) O D j jp)) ≤
      Module.finrank ℤ_[p] (Ljj (r := r) p (gmB D) j jp) := by
  classical
  let W : Submodule ℚ_[p] (MvPolynomial (GM.M.BVar N r D.T.t) ℚ_[p]) :=
    Submodule.span ℚ_[p] (SetLike.coe (Ljj (r := r) p (gmB D) j jp))
  haveI hWfd : FiniteDimensional ℚ_[p] W := Ljj_span_fd (p := p) (r := r) (gmB D) j jp
  let Pk : MvPolynomial (BVar N r D.T.t) (KK O) :=
    ((∏ i : Fin D.T.t, BlockData.Ehat (r := r) O D i ^ j i) * BlockData.Eplus (r := r) O D ^ jp *
      ∏ i : Fin D.T.t, MvPolynomial.X (scalZ N r D.T.t i.castSucc) ^ D.T.z i) *
      MvPolynomial.X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus
  let mι : MvPolynomial (GM.M.BVar N r D.T.t) ℚ_[p] →+* MvPolynomial (BVar N r D.T.t) (KK O) :=
    MvPolynomial.map ι
  let fA : MvPolynomial (GM.M.BVar N r D.T.t) ℚ_[p] →+ MvPolynomial (BVar N r D.T.t) (KK O) :=
    (AddMonoidHom.mulLeft Pk).comp mι.toAddMonoidHom
  have hfA : ∀ u, fA u = Pk * mι u := fun u => rfl
  have hadd : ∀ u v, fA (u + v) = fA u + fA v := fun u v => map_add fA u v
  have hsmul : ∀ (c : ℚ_[p]) u, fA (c • u) = ι c • fA u := by
    intro c u
    rw [hfA, hfA, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul]
    simp only [mι, MvPolynomial.map_C]
    ring
  let T : Submodule (KK O) (MvPolynomial (BVar N r D.T.t) (KK O)) :=
    Submodule.span (KK O) (fA '' (W : Set _))
  have hT : Module.finrank (KK O) T ≤ Module.finrank ℚ_[p] W :=
    finrank_span_image_le ι fA hadd hsmul W
  let bW := Module.finBasis ℚ_[p] W
  have hTle : T ≤ Submodule.span (KK O) (Set.range fun i => fA (bW i : MvPolynomial _ ℚ_[p])) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w = ∑ i, (bW.repr ⟨w, hw⟩ i) • (bW i : MvPolynomial _ ℚ_[p]) := by
      have h1 : ((∑ i, (bW.repr ⟨w, hw⟩ i) • bW i : W) : MvPolynomial _ ℚ_[p]) = w := by
        rw [bW.sum_repr]
      refine h1.symm.trans ?_
      simp only [Submodule.coe_sum, Submodule.coe_smul]

    rw [hw', map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : FiniteDimensional (KK O)
      (Submodule.span (KK O) (Set.range fun i => fA (bW i : MvPolynomial _ ℚ_[p]))) :=
    FiniteDimensional.span_of_finite (KK O) (Set.finite_range _)
  haveI : FiniteDimensional (KK O) T :=
    Submodule.finiteDimensional_of_le hTle
  have hbase : ∀ y0 ∈ GM.M.YZ (r := r) p ((gmB D).lettersAt j jp) D.T.J D.T.thr,
      ∀ g0 ∈ GM.M.XiPolZ p N r D.T.t (D.B - jp),
      Pk * rename (chainEmb N r D.T.t) (MvPolynomial.map ι y0) * MvPolynomial.map ι g0 ∈ T := by
    intro y0 hy0 g0 hg0
    have h1 : rename (GM.M.chainEmb N r D.T.t) y0 * g0 ∈ Ljj (r := r) p (gmB D) j jp := by
      unfold Ljj
      exact Submodule.subset_span ⟨y0, hy0, g0, hg0, rfl⟩
    have hmem : rename (GM.M.chainEmb N r D.T.t) y0 * g0 ∈ W := Submodule.subset_span h1
    have := Submodule.subset_span (R := KK O) (Set.mem_image_of_mem fA hmem)
    rw [hfA] at this
    simp only [mι, map_mul, MvPolynomial.map_rename] at this
    rw [← mul_assoc] at this
    exact this
  have hstep : ∀ a ∈ Submodule.span (KK O)
        (MvPolynomial.map ι '' (GM.M.YZ (r := r) p ((gmB D).lettersAt j jp) D.T.J D.T.thr : Set _)),
      ∀ c ∈ Submodule.span (KK O)
        (MvPolynomial.map ι '' (GM.M.XiPolZ p N r D.T.t (D.B - jp) : Set _)),
      Pk * rename (chainEmb N r D.T.t) a * c ∈ T := by
    intro a ha c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨g0, hg0, rfl⟩ := hc
      induction ha using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨y0, hy0, rfl⟩ := ha
        exact hbase y0 hy0 g0 hg0
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add (f := _), mul_add, add_mul]
        exact T.add_mem hx hy
      | smul k x _ hx =>
        rw [map_smul, mul_smul_comm, smul_mul_assoc]
        exact T.smul_mem k hx
    | zero => simp
    | add x y _ _ hx hy =>
      rw [mul_add]
      exact T.add_mem hx hy
    | smul k x _ hx =>
      rw [mul_smul_comm]
      exact T.smul_mem k hx
  have hgens : Submodule.span (KK O) (BlockData.gens (r := r) O D j jp) ≤ T := by
    rw [Submodule.span_le]
    rintro x ⟨y, hy, g, hg, rfl⟩
    exact hstep _ (hY O p ι N r (D.lettersAt j jp) D.T.q D.T.J D.T.thr y hy) g (xi_span ι g hg)
  calc Module.finrank (KK O) (Submodule.span (KK O) (BlockData.gens (r := r) O D j jp))
      ≤ Module.finrank (KK O) T :=
        LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hgens)
          (Submodule.inclusion_injective hgens)
    _ ≤ Module.finrank ℚ_[p] W := hT
    _ = Module.finrank ℤ_[p] (Ljj (r := r) p (gmB D) j jp) := (finrank_Ljj_span (gmB D) j jp).symm

theorem restBClvl_of (hY : RestYbc) : RestBClvl C0 CE1 CE2 X := by
  intro aTop _ aPlus _ b _ l _
  exact finrank_span_blockData_gens (O := X.O) (r := X.r) (iotaX X) hY
    (blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b) l.1 l.2

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem sum_finrank_le_of_indep {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V] [DecidableEq ι]
    (f : ι → Submodule K V) (hf : iSupIndep f) (T : Submodule K V) [FiniteDimensional K T] (s : Finset ι)
    (hle : ∀ i ∈ s, f i ≤ T) : ∑ i ∈ s, Module.finrank K (f i) ≤ Module.finrank K T := by
  have key : ∀ s : Finset ι, (∀ i ∈ s, f i ≤ T) →
      (⨆ i ∈ s, f i) ≤ T ∧ ∑ i ∈ s, Module.finrank K (f i) = Module.finrank K (⨆ i ∈ s, f i : Submodule K V) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      have h0 : (⨆ i ∈ (∅ : Finset ι), f i) = ⊥ := le_bot_iff.1 (iSup₂_le fun i hi => by simp at hi)
      rw [h0, finrank_bot, Finset.sum_empty]
      exact ⟨bot_le, rfl⟩
    | insert a s ha ih =>
      intro h
      obtain ⟨h1, h2⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hfa : f a ≤ T := h a (Finset.mem_insert_self a s)
      have e : (⨆ i ∈ insert a s, f i) = f a ⊔ ⨆ i ∈ s, f i := by
        rw [Finset.iSup_insert]
      haveI : FiniteDimensional K (f a) := Submodule.finiteDimensional_of_le hfa
      haveI : FiniteDimensional K (⨆ i ∈ s, f i : Submodule K V) := Submodule.finiteDimensional_of_le h1
      have hd : Disjoint (f a) (⨆ i ∈ s, f i) := hf.disjoint_biSup ha
      refine ⟨by rw [e]; exact sup_le hfa h1, ?_⟩
      rw [Finset.sum_insert ha, h2, e]
      have := Submodule.finrank_sup_add_finrank_inf_eq (f a) (⨆ i ∈ s, f i)
      rw [hd.eq_bot, finrank_bot, add_zero] at this
      omega
  obtain ⟨h1, h2⟩ := key s hle
  rw [h2]
  exact Submodule.finrank_mono h1

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem span_SSZ_fin (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r) :
    FiniteDimensional ℚ_[X.p] (Submodule.span ℚ_[X.p]
      (((gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r) :
        Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])) :
          Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p]))) := by
  set Dd := blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b with hDd
  set V0 := Submodule.span ℚ_[X.p]
    (((gmB Dd).SSZ X.p (r := X.r) : Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) :
      Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) with hV0
  set W := Submodule.span (KK X.O) ((Dd.SSZ X.O (r := X.r) : Submodule X.O (MvPolynomial (BVar (2 * X.s + 1) X.r Dd.T.t) (KK X.O))) :
      Set (MvPolynomial (BVar (2 * X.s + 1) X.r Dd.T.t) (KK X.O))) with hW
  show FiniteDimensional ℚ_[X.p] V0
  haveI : FiniteDimensional (KK X.O) W := span_SSZ_finite Dd
  have hmemW : ∀ x ∈ V0, MvPolynomial.map (iotaX X) x ∈ W := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact map_SSZ (ι := iotaX X) (iotaX_int X) Dd x hx
    | zero => rw [map_zero]; exact W.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact W.add_mem hx hy
    | smul a x _ hx => rw [map_smul_Q]; exact W.smul_mem _ hx
  refine Module.rank_lt_aleph0_iff.1 (lt_of_le_of_lt (_root_.rank_le (n := Module.finrank (KK X.O) W) fun s hs => ?_)
    (Cardinal.natCast_lt_aleph0))
  have hli : LinearIndependent ℚ_[X.p] (fun i : s => ((i : V0) : MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) :=
    hs.map' V0.subtype (Submodule.ker_subtype V0)
  have hli2 := li_map (iotaX X) _ hli
  let w : s → W := fun i => ⟨MvPolynomial.map (iotaX X) (i : V0).1, hmemW _ (i : V0).2⟩
  have hli3 : LinearIndependent (KK X.O) w := LinearIndependent.of_comp W.subtype hli2
  have h := hli3.fintype_card_le_finrank
  simpa using h

theorem sum_gens_le (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N) (hB : G.BlockOK)
    (hr : 1 ≤ r) (s : Finset ((Fin G.T.t → ℕ) × ℕ)) (hs : ∀ x ∈ s, G.LevelOK x.1 x.2)
    [FiniteDimensional ℚ_[p] (Submodule.span ℚ_[p] ((G.SSZ p (r := r) :
      Submodule ℤ_[p] (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])) : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])))] :
    ∑ x ∈ s, Module.finrank ℚ_[p] (Submodule.span ℚ_[p] (G.gens p (r := r) x.1 x.2)) ≤
      Module.finrank ℚ_[p] (Submodule.span ℚ_[p] ((G.SSZ p (r := r) :
        Submodule ℤ_[p] (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])) : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]))) := by
  classical
  have hind := (Formalism.GM.semisimple_direct_sum p N r G hB hr).1
  let g : {x // x ∈ s} → {ij : (Fin G.T.t → ℕ) × ℕ // G.LevelOK ij.1 ij.2} := fun y => ⟨y.1, hs y.1 y.2⟩
  have hg : Function.Injective g := fun y y' h => by
    apply Subtype.ext
    have := congrArg Subtype.val h
    exact this
  have hind' := iSupIndep.comp hind hg
  rw [← Finset.sum_attach]
  refine sum_finrank_le_of_indep _ hind' _ s.attach fun y _ => ?_
  apply Submodule.span_le.2
  intro z hz
  apply Submodule.subset_span
  show z ∈ ((G.SSZ p (r := r) : Submodule ℤ_[p] (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])) :
    Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]))
  unfold Formalism.GM.M.BlockData.SSZ
  exact Submodule.subset_span (Set.mem_iUnion.2 ⟨y.1.1, Set.mem_iUnion.2 ⟨y.1.2, Set.mem_iUnion.2 ⟨hs y.1 y.2, hz⟩⟩⟩)

theorem restSumSpan_proved : RestSumSpan C0 CE1 CE2 X := by
  classical
  intro aTop _ aPlus _ b _
  haveI := span_SSZ_fin C0 CE1 CE2 X aTop aPlus b
  have hr : 1 ≤ X.r := Nat.pos_of_ne_zero X.hm
  refine sum_gens_le X.p (gB C0 CE1 CE2 X aTop aPlus b) (gB_blockOK C0 CE1 CE2 X aTop aPlus b) hr
    (lv C0 CE1 CE2 X aTop b) (fun x hx => ?_)
  rw [lv_eq C0 CE1 CE2 X aTop aPlus b] at hx
  unfold levels at hx
  exact (Finset.mem_filter.1 hx).2

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

theorem exists_low (lo ρ P : ℕ) (hP : 0 < P) (hρ : ρ ≤ lo) :
    ∃ v, lo ≤ v ∧ v + 1 ≤ lo + P ∧ ρ ≤ v ∧ P ∣ v - ρ := by
  obtain ⟨q, r, hr, hd⟩ : ∃ q r, r < P ∧ lo - ρ = P * q + r :=
    ⟨(lo - ρ) / P, (lo - ρ) % P, Nat.mod_lt _ hP, (Nat.div_add_mod _ _).symm⟩
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · refine ⟨lo, le_rfl, by omega, hρ, ⟨q, by omega⟩⟩
  · refine ⟨lo + (P - r), by omega, by omega, by omega, ⟨q + 1, ?_⟩⟩
    rw [Nat.mul_add, Nat.mul_one]
    omega

theorem exists_high (hi ρ P : ℕ) (hP : 0 < P) (hρ : ρ ≤ hi) :
    ∃ v, v ≤ hi ∧ hi + 1 ≤ v + P ∧ ρ ≤ v ∧ P ∣ v - ρ := by
  obtain ⟨q, r, hr, hd⟩ : ∃ q r, r < P ∧ hi - ρ = P * q + r :=
    ⟨(hi - ρ) / P, (hi - ρ) % P, Nat.mod_lt _ hP, (Nat.div_add_mod _ _).symm⟩
  exact ⟨hi - r, by omega, by omega, by omega, ⟨q, by omega⟩⟩

section Eps

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

theorem Yl_bound (hFree : RestFree C0 CE1 CE2 X) {dl : DCl X} (hdl : dl ∈ clSet C0 CE1 CE2 X) {a : Fin X.s → ℕ}
    (ha : a ∈ cbox C0 CE1 CE2 X dl) {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X} (hx : x ∈ idx C0 CE1 CE2 X dl a)
    (i : Fin (X.S C0 CE1 CE2).t)
    (hroom : X.L.a + 2 * (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) ≤
      ⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊) :
    ((⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℕ) : ℝ) - X.L.a -
        ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
  set l := uTop (X.S C0 CE1 CE2) i with hl
  set P := (X.S C0 CE1 CE2).P X.p l with hP
  set σ := ∑ c : Fin (X.r + 1), dl.2 l c with hσ
  set N := ⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ with hN
  have hP1 : 1 ≤ P := hS.P1 l
  have hdl' : dl ∈ digSet C0 CE1 CE2 X ×ˢ digSet C0 CE1 CE2 X := hdl
  have h2 : dl.2 ∈ digSet C0 CE1 CE2 X := (Finset.mem_product.1 hdl').2
  have hdig : ∀ c, dl.2 l c < P := fun c =>
    Finset.mem_range.1 (Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 h2 l) c)
  have hsum : σ < (X.r + 1) * P := by
    have := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin (X.r + 1))))
      Finset.univ_nonempty (fun c _ => hdig c)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using this
  have hσA : σ ≤ X.L.a := by
    have hkP := hS.kP l
    have hkb := hS.kb
    have hsR : (σ : ℝ) < ((X.r : ℝ) + 1) * (P : ℝ) := by exact_mod_cast hsum
    have hP1R : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP1
    have hr0 : (0 : ℝ) ≤ (X.r : ℝ) := Nat.cast_nonneg _
    have hb0 : (0 : ℝ) ≤ X.L.b' := by nlinarith
    have hA0 : (0 : ℝ) ≤ (X.L.a : ℝ) := Nat.cast_nonneg _
    have : (σ : ℝ) < (X.L.a : ℝ) := by nlinarith
    exact_mod_cast this.le
  obtain ⟨vlo, hlo1, hlo2, hlo3, hlo4⟩ := exists_low X.L.a σ P (by omega) hσA
  obtain ⟨vhi, hhi1, hhi2, hhi3, hhi4⟩ := exists_high N σ P (by omega) (by omega)
  have hWlo : vlo ∈ Wl C0 CE1 CE2 X dl l := by
    simp only [Wl, flipOneThree.Inst.winA, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hlo1, by omega⟩, hlo3, hlo4⟩
  have hWhi : vhi ∈ Wl C0 CE1 CE2 X dl l := by
    simp only [Wl, flipOneThree.Inst.winA, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hhi1⟩, hhi3, hhi4⟩
  have hry : x.fst.ry = dl.2 := by
    have hx' := (Finset.mem_sigma.1 hx).1
    simp only [Finset.mem_filter] at hx'
    exact congrArg Prod.snd hx'.2
  have hall : ∀ a' ∈ cbox C0 CE1 CE2 X dl, x ∈ idx C0 CE1 CE2 X dl a' := fun a' ha' =>
    (hFree dl hdl a ha a' ha') ▸ hx
  have hroomL : LvlRoom C0 CE1 CE2 X dl x.snd := lvlRoom_of ha hry hall
  have hx1 : x.2.1 i ≤ (vlo - σ) / P := hroomL i vlo hWlo
  obtain ⟨qlo, hqlo⟩ := hlo4
  obtain ⟨qhi, hqhi⟩ := hhi4
  have hPpos : 0 < P := by omega
  have hdlo : (vlo - σ) / P = qlo := by rw [hqlo]; exact Nat.mul_div_cancel_left _ hPpos
  have hdhi : (vhi - σ) / P = qhi := by rw [hqhi]; exact Nat.mul_div_cancel_left _ hPpos
  have hmlo : cm C0 CE1 CE2 X dl x.2 i vlo ∈ Nl C0 CE1 CE2 X dl x.2 i := by
    unfold Nl; exact Finset.mem_image_of_mem _ hWlo
  have hmhi : cm C0 CE1 CE2 X dl x.2 i vhi ∈ Nl C0 CE1 CE2 X dl x.2 i := by
    unfold Nl; exact Finset.mem_image_of_mem _ hWhi
  have hinf : sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) ≤ cm C0 CE1 CE2 X dl x.2 i vlo :=
    Nat.sInf_le (Finset.mem_coe.2 hmlo)
  have hsup : cm C0 CE1 CE2 X dl x.2 i vhi ≤ (Nl C0 CE1 CE2 X dl x.2 i).sup id :=
    Finset.le_sup (f := id) hmhi
  have hclo : cm C0 CE1 CE2 X dl x.2 i vlo = qlo - x.2.1 i := by
    show (vlo - σ) / P - x.2.1 i = _; rw [hdlo]
  have hchi : cm C0 CE1 CE2 X dl x.2 i vhi = qhi - x.2.1 i := by
    show (vhi - σ) / P - x.2.1 i = _; rw [hdhi]
  have hY : (XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i =
      (Nl C0 CE1 CE2 X dl x.2 i).sup id - sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) + 1 := rfl
  rw [hdlo] at hx1
  have hvv : vlo < vhi := by omega
  have hqq : qlo ≤ qhi := by
    by_contra hc
    push_neg at hc
    have : P * qhi < P * qlo := Nat.mul_lt_mul_of_pos_left hc hPpos
    omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hqq
  have hYd : d + 1 ≤ (XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i := by
    rw [hY]; omega
  have hmul : (d + 1) * P ≤ (XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i * P := Nat.mul_le_mul_right _ hYd
  rw [Nat.add_mul, one_mul, mul_comm d P] at hmul
  rw [Nat.mul_add] at hqhi
  have hnat : N ≤ (XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i * P + X.L.a + P := by
    generalize P * qlo = u at *
    generalize P * d = w at *
    generalize (XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i * P = t at *
    omega
  have hR : ((N : ℕ) : ℝ) ≤ (((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i * P + X.L.a + P : ℕ) : ℝ) := by
    exact_mod_cast hnat
  push_cast at hR
  linarith

end Eps

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
