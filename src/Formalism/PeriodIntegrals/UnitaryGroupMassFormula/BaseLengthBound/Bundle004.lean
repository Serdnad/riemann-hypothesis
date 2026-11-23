module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.Bundle001
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ReductionUniformizerSmulMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.Bundle002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle030
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle029
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.YmDeriv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem inc_cast {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) {u u' : WeightFamilies.Wt D j}
    (h : u = u') (F : B.Cusp j u) : X.inc u' (h ▸ F) = X.inc u F := by
  subst h; rfl

theorem one_le_of_nonneg_of_ne {a : WithTop ℤ} (h0 : 0 ≤ a) (h1 : a ≠ 0) : 1 ≤ a := by
  induction a using WithTop.recTopCoe with
  | top => exact le_top
  | coe n =>
    have h2 : (0 : ℤ) ≤ n := by exact_mod_cast h0
    have h3 : n ≠ 0 := fun h => h1 (by rw [h]; rfl)
    exact_mod_cast (show (1 : ℤ) ≤ n by omega)

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem wfr_eq (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (jj : Fin G.N) :
    fr0 X la G.w 1 ⟨emb X la G.N (X.inc _ ((add_zero_weight_one_eq wL).symm ▸ G.w jj : B.Cusp j (addL (wt0 D j) wL 1))),
      emb_mem_Vw X la G.N _ _⟩ = wfr G la jj := by
  unfold wfr
  congr 1
  exact Subtype.ext (congrArg (emb X la G.N) (inc_cast X (add_zero_weight_one_eq wL).symm (G.w jj)))

theorem ord_wfr_nonneg (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B)
    (hT : Q.InTie S) (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) (ζ : PtsG G la) (jj : Fin G.N) :
    0 ≤ ord (unifO X la G.N) ζ (toOsK X la G.w (wfr G la jj)) := by
  obtain ⟨hd1, hd2, -, -, -, hk, -⟩ := hT ζ
  have e := hk 1 ((add_zero_weight_one_eq wL).symm ▸ G.w jj : B.Cusp j (addL (wt0 D j) wL 1))
  rw [wfr_eq, inc_cast] at e
  have hv : X.depth S.sW wL la (Q.y ζ) ≤ X.vAt la (Q.y ζ) (X.inc wL (G.w jj)) := iInf₂_le _ (hw jj)
  have hd : X.depth S.sW wL la (Q.y ζ) = (((X.depth S.sW wL la (Q.y ζ)).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hd1 hd2).symm
  have hv' : (((X.depth S.sW wL la (Q.y ζ)).toReal : ℝ) : EReal) ≤ X.vAt la (Q.y ζ) (X.inc wL (G.w jj)) := by
    rw [← hd]; exact hv
  have hb := ereal_bound (ep := ep (unifO X la G.N) ζ) (T := 1) hd hv'
  have key : (((0 : ℤ) : ℝ) : EReal) ≤ toE (ord (unifO X la G.N) ζ (toOsK X la G.w (wfr G la jj))) := by
    rw [e]
    refine le_trans (le_of_eq ?_) hb
    simp
  simpa using le_of_coe_le_toE key

theorem one_eq_sum_wfr (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) :
    (1 : ↥(Frac0 X la G.w)) = ∑ k, (@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ (Tv X la G.N (0, k))) • wfr G la k := by
  have h1 : frac X la G.w 1 (sec X la G.w 0) = 1 := by rw [frac_apply, pow_one, section_mul_inverse_eq_one]
  have h2 : frac X la G.w 1 (sec X la G.w 0) = ∑ k, (@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ (Tv X la G.N (0, k))) •
      frac X la G.w 1 (emb X la G.N (X.inc wL (G.w k))) := by

    rw [sec, map_sum]
    simp only [map_smul]
  apply Subtype.ext
  rw [OneMemClass.coe_one, ← h1, h2, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

theorem one_eq_sum_toOsK (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) :
    (1 : OsK X la G.w) = ∑ k, algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N (0, k)) *
      toOsK X la G.w (wfr G la k) := by

  rw [← map_one (toOsK X la G.w), one_eq_sum_wfr G la, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Algebra.smul_def, (IsScalarTower.algebraMap_apply (Op X la G.N) (Kp X la G.N) (OsK X la G.w) _).symm]

theorem one_le_ord_sum (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (ζ : PtsG G la) [IsDVRAt ζ]
    (h : IsUnif (OsK X la G.w) (unifO X la G.N)) (s : Finset (Fin G.N)) (f : Fin G.N → OsK X la G.w)
    (hf : ∀ k, 1 ≤ ord (unifO X la G.N) ζ (f k)) : 1 ≤ ord (unifO X la G.N) ζ (∑ k ∈ s, f k) := by
  classical
  refine Finset.induction_on s (by rw [Finset.sum_empty, ord_zero ζ h]; exact le_top) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha]
  exact (le_min (hf a) ih).trans (ord_add ζ h _ _)

theorem column_holds : Column := by
  intro D B P j X ka wL wF G la Q S CRm T c hOk hw ζ
  have hC := hOk.2.1
  have hT := hOk.2.2.1
  have h := isUnif_of_curve Q hC
  have := isDVRAt_of_curve Q hC ζ
  refine ⟨fun jj => ord_wfr_nonneg G la Q S hT hw ζ jj, ?_⟩
  by_contra hne
  push Not at hne
  have hall : ∀ k, 1 ≤ ord (unifO X la G.N) ζ (algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N (0, k)) *
      toOsK X la G.w (wfr G la k)) := by
    intro k
    rw [ord_mul ζ h]
    have h0 : 0 ≤ ord (unifO X la G.N) ζ (algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N (0, k))) :=
      ord_nonneg ζ h (Subalgebra.algebraMap_mem _ _)
    have h1 := one_le_of_nonneg_of_ne (ord_wfr_nonneg G la Q S hT hw ζ k) (hne k)
    simpa using add_le_add h0 h1
  have h2 := one_le_ord_sum G la ζ h Finset.univ _ hall
  rw [← one_eq_sum_toOsK, ord_one ζ h] at h2
  exact absurd (WithTop.coe_le_coe.1 (show ((1 : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ) from h2)) (by norm_num)

end PoleLengthBounds
end
end

section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem taylorSpanLeBound : TaylorSpanLeBound := by
  intro D B P j X ka wL wF G la Q S CRm T c hOk hw hth
  let G' : GlobalFamilyData X (addL wF wL T) wL wF :=
    { N := G.N, w := G.w, del := G.del, th' := G.th', rz := G.rz, alz := G.alz, th0 := G.th0,
      zc := fun _ => 0, rq := 0, th := Fin.elim0, iet := G.iet, et := G.et, mx := G.mx }
  let Q' : LocalPointData G' la := ⟨Q.y, Q.g0, Q.c⟩
  exact reduced_generators_le (G := G') Q' S hOk.2.1 hOk.2.2.1 hw hth

end PoleLengthBounds
end
end

section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

namespace THs

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
  (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))

theorem mem_pow_smul_HK_iff (u : WeightFamilies.Wt D j) (a : ℕ) (z : Lw X la G.w) :
    z ∈ Jid X la G.w ^ a • HK X la G.w u ↔ z ∈ JHfr X la G.w u a := by
  rw [Jid_pow_smul_HK, mem_JHs, mem_JHfr]

theorem mem_smul_top_iff (u : WeightFamilies.Wt D j) (a : ℕ) (x : ↥(HK X la G.w u)) :
    x ∈ Jid X la G.w ^ a • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w u)) ↔
      (x : Lw X la G.w) ∈ Jid X la G.w ^ a • HK X la G.w u := by
  have h : (Jid X la G.w ^ a • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w u))).map (HK X la G.w u).subtype =
      Jid X la G.w ^ a • HK X la G.w u := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  rw [← h]
  exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hxy⟩ => (Subtype.ext hxy : y = x) ▸ hy⟩

theorem smul_eq_mul' (f : ↥(Frac0 X la G.w)) (z : Lw X la G.w) : f • z = (f : Lw X la G.w) * z := rfl

def hs (β : Idx D j G.N →₀ ℕ) (z : Lw X la G.w) : Lw X la G.w := hasse X la G.w β z

theorem hs_mul (β : Idx D j G.N →₀ ℕ) (a b : Lw X la G.w) :
    hs G la β (a * b) = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal β, hs G la q.1 a * hs G la q.2 b :=
  hasse_mul X la G.w β a b

theorem hs_add (β : Idx D j G.N →₀ ℕ) (a b : Lw X la G.w) : hs G la β (a + b) = hs G la β a + hs G la β b :=
  (hasse X la G.w β).map_add a b

theorem hs_sum {ι : Type} (s : Finset ι) (β : Idx D j G.N →₀ ℕ) (f : ι → Lw X la G.w) :
    hs G la β (∑ i ∈ s, f i) = ∑ i ∈ s, hs G la β (f i) :=
  map_sum (hasse X la G.w β) f s

theorem hs_zero (a : Lw X la G.w) : hs G la 0 a = a := hasse_zero X la G.w a

theorem one_mem_hasse_kernel : (1 : Lw X la G.w) ∈ HK X la G.w (wt0 D j) :=
  (mem_HK X la G.w).2 ((mem_Frac0 X la G.w).1 (Subalgebra.one_mem _))

theorem mul_mem_HK {u : WeightFamilies.Wt D j} {h m : Lw X la G.w} (hh : h ∈ HK X la G.w (wt0 D j))
    (hm : m ∈ HK X la G.w u) : h * m ∈ HK X la G.w u := by
  have := mul_mem_Hfr X la G.w ((mem_HK X la G.w).1 hh) ((mem_HK X la G.w).1 hm)
  rw [zero_weight_add] at this
  exact (mem_HK X la G.w).2 this

theorem mul_mem_J_smul_HK {u : WeightFamilies.Wt D j} {z m : Lw X la G.w}
    (hz : z ∈ Jid X la G.w • HK X la G.w (wt0 D j)) (hm : m ∈ HK X la G.w u) :
    z * m ∈ Jid X la G.w • HK X la G.w u := by
  refine Submodule.smul_induction_on (p := fun z => z * m ∈ Jid X la G.w • HK X la G.w u) hz ?_ ?_
  · intro r hr n hn
    show (r • n) * m ∈ _
    rw [smul_eq_mul' G la, mul_assoc, ← smul_eq_mul' G la]
    exact Submodule.smul_mem_smul hr (mul_mem_HK G la hn hm)
  · intro x y hx hy
    show (x + y) * m ∈ _
    rw [add_mul]
    exact Submodule.add_mem _ hx hy

theorem hasse_mem_pow_smul_HK (u : WeightFamilies.Wt D j) (β : Idx D j G.N →₀ ℕ) (a : ℕ) (z : Lw X la G.w)
    (hz : z ∈ Jid X la G.w ^ a • HK X la G.w u) :
    hs G la β z ∈ Jid X la G.w ^ (a - β.sum fun _ n => n) • HK X la G.w u :=
  (mem_pow_smul_HK_iff G la u _ _).2 (hasse_jid_power X la G.w u β a z ((mem_pow_smul_HK_iff G la u a z).1 hz))

theorem ym_mem (γ : Fin (WeightFamilies.dimY D j) → ℕ) :
    ((ym G la γ : ↥(Frac0 X la G.w)) : Lw X la G.w) ∈ Jid X la G.w ^ (∑ i, γ i) • HK X la G.w (wt0 D j) := by
  have := Submodule.smul_mem_smul (prod_sfr_mem X la G.w γ) (one_mem_hasse_kernel G la)
  rw [smul_eq_mul', mul_one] at this
  exact this

theorem hasse_mem_HK (u : WeightFamilies.Wt D j) (β : Idx D j G.N →₀ ℕ) {z : Lw X la G.w} (hz : z ∈ HK X la G.w u) :
    hs G la β z ∈ HK X la G.w u :=
  (mem_HK X la G.w).2 (hasse_presentation X la G.w u β z ((mem_HK X la G.w).1 hz))

theorem bcol_size {N : ℕ} (jj : Fin N) (α : Fin (WeightFamilies.dimY D j) → ℕ) :
    ((bcol (D := D) (j := j) jj α).sum fun _ n => n) = ∑ i, α i := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp [bcol]

theorem size_eq_degree {N : ℕ} (f : Idx D j N →₀ ℕ) : (f.sum fun _ n => n) = Finsupp.degree f := rfl

end THs

open THs in
theorem taylorHasse_of (hY : YmDeriv) : TaylorHasse := by
  intro D B P j X ka wL wF G la k x cf hx jj α hα h
  have hk : ∑ i, α i = k := (Finset.Nat.mem_antidiagonalTuple).1 hα
  have hβs : ((bcol (D := D) (j := j) jj α).sum fun _ n => n) = k := by rw [bcol_size, hk]
  have huC : uC G la jj α = toOsK X la G.w (wfr G la jj ^ k) := by
    simp only [uC, map_pow, Finset.prod_pow_eq_pow_sum, hk]
  have hsm : toOsK X la G.w (wfr G la jj ^ k) • toA0K X la G.w wF (cf α) =
      toA0K X la G.w wF ((wfr G la jj ^ k) • cf α) := by
    rw [map_smul]
    exact algebraMap_smul (OsK X la G.w) (wfr G la jj ^ k) (toA0K X la G.w wF (cf α))
  rw [huC, hsm, ← sub_eq_zero, ← map_sub, reduction_eq_zero_iff_mem_ideal_smul, ← pow_one (Jid X la G.w), mem_smul_top_iff,
    Submodule.coe_sub, Submodule.coe_smul, pow_one]
  rw [mem_smul_top_iff, Submodule.coe_sub, Submodule.coe_sum] at hx
  set rr : Lw X la G.w := (x : Lw X la G.w) - ∑ γ ∈ mon D j k, ((ym G la γ • cf γ : ↥(HK X la G.w wF)) : Lw X la G.w)
    with hrr
  have hxe : (x : Lw X la G.w) = rr + ∑ γ ∈ mon D j k, (ym G la γ : Lw X la G.w) * (cf γ : Lw X la G.w) := by
    have e : ∑ γ ∈ mon D j k, ((ym G la γ • cf γ : ↥(HK X la G.w wF)) : Lw X la G.w) =
        ∑ γ ∈ mon D j k, (ym G la γ : Lw X la G.w) * (cf γ : Lw X la G.w) :=
      Finset.sum_congr rfl fun γ _ => by rw [Submodule.coe_smul, smul_eq_mul']
    rw [hrr, e, sub_add_cancel]

  have h1 : hs G la (bcol jj α) rr ∈ Jid X la G.w • HK X la G.w wF := by
    have := hasse_mem_pow_smul_HK G la wF (bcol jj α) (k + 1) rr hx
    rwa [hβs, Nat.add_sub_cancel_left, pow_one] at this

  have h2 : ∀ γ ∈ mon D j k, hs G la (bcol jj α) ((ym G la γ : Lw X la G.w) * (cf γ : Lw X la G.w)) -
      (if γ = α then ((wfr G la jj ^ k : ↥(Frac0 X la G.w)) : Lw X la G.w) * (cf α : Lw X la G.w) else 0) ∈
        Jid X la G.w • HK X la G.w wF := by
    intro γ hγ
    have hγk : ∑ i, γ i = k := (Finset.Nat.mem_antidiagonalTuple).1 hγ
    have hmem : ((bcol jj α, 0) : (Idx D j G.N →₀ ℕ) × (Idx D j G.N →₀ ℕ)) ∈ Finset.HasAntidiagonal.antidiagonal (bcol jj α) := by
      rw [Finset.HasAntidiagonal.mem_antidiagonal, add_zero]
    rw [hs_mul, ← Finset.add_sum_erase _ _ hmem]
    have hYg := hY G la jj γ α (by rw [hγk, hk])
    change hs G la _ _ = _ at hYg
    have htop : hs G la (bcol jj α) (ym G la γ : Lw X la G.w) * hs G la 0 (cf γ : Lw X la G.w) =
        (if γ = α then ((wfr G la jj ^ k : ↥(Frac0 X la G.w)) : Lw X la G.w) * (cf α : Lw X la G.w) else 0) := by
      rw [hYg, hs_zero]
      split_ifs with he
      · subst he; rw [hk]; push_cast; rfl
      · rw [zero_mul]
    simp only at htop ⊢
    rw [htop, add_sub_cancel_left]
    refine Submodule.sum_mem _ fun q hq => ?_
    obtain ⟨hne, hq⟩ := Finset.mem_erase.1 hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hq2 : q.2 ≠ 0 := by
      intro h0
      apply hne
      rw [h0, add_zero] at hq
      exact Prod.ext hq h0
    have hdeg : Finsupp.degree q.1 + Finsupp.degree q.2 = k := by
      rw [← map_add (f := _), hq, ← size_eq_degree, hβs]
    have hpos : Finsupp.degree q.2 ≠ 0 := fun h0 => hq2 ((Finsupp.degree_eq_zero_iff _).1 h0)
    have hA := hasse_mem_pow_smul_HK G la (wt0 D j) q.1 (∑ i, γ i) _ (ym_mem G la γ)
    rw [hγk, size_eq_degree] at hA
    have hA' : hs G la q.1 (ym G la γ : Lw X la G.w) ∈ Jid X la G.w • HK X la G.w (wt0 D j) :=
      Submodule.smul_mono_left (Ideal.pow_le_self (by omega)) hA
    exact mul_mem_J_smul_HK G la hA' (hasse_mem_HK G la wF q.2 (cf γ).2)
  change hs G la (bcol jj α) (x : Lw X la G.w) - _ ∈ _
  rw [hxe, hs_add, hs_sum]
  have hsum : ∑ γ ∈ mon D j k, (if γ = α then ((wfr G la jj ^ k : ↥(Frac0 X la G.w)) : Lw X la G.w) *
      (cf α : Lw X la G.w) else 0) = (wfr G la jj ^ k : ↥(Frac0 X la G.w)) • (cf α : Lw X la G.w) := by
    rw [Finset.sum_ite_eq', if_pos hα, smul_eq_mul']
  rw [← hsum, add_sub_assoc, ← Finset.sum_sub_distrib]
  exact Submodule.add_mem _ h1 (Submodule.sum_mem _ h2)

theorem taylorHasse_holds : TaylorHasse := taylorHasse_of PI.PoleLengthCount.ymDeriv

end PoleLengthBounds
end
end
