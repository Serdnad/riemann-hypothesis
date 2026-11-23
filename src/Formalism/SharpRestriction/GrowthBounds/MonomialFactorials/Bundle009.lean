module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle006
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.LettersExt
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

open MvPolynomial Finset Formalism.MainNotions.G

def cmap {K L σ : Type} [CommRing K] [CommRing L] (f : K →+ L) (y : MvPolynomial σ K) : MvPolynomial σ L :=
  ∑ m ∈ y.support, monomial m (f (y.coeff m))

def RestFunY : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (p : ℕ) [Fact p.Prime] (ι : ℚ_[p] →+* KK O) (N r : ℕ) [NeZero r]
    (LL : ChainLetters N) (q : ℕ) (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (f : KK O →+ ℚ_[p]),
    (∀ (a : ℚ_[p]) (x : KK O), f (ι a * x) = a * f x) →
    ∀ y ∈ Yjt (KK O) (r := r) LL J M, cmap f y ∈ Formalism.GM.M.Y p (r := r) (Formalism.MainNotions.G.SymmetricFormBlocks.gmL LL) J M

def RestDecomp : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (p : ℕ) [Fact p.Prime] (ι : ℚ_[p] →+* KK O) (σ : Type)
    (y : MvPolynomial σ (KK O)),
    ∃ (n : ℕ) (b : Fin n → KK O) (f : Fin n → (KK O →+ ℚ_[p])),
      (∀ k (a : ℚ_[p]) (x : KK O), f k (ι a * x) = a * f k x) ∧
      y = ∑ k, b k • map ι (cmap (f k) y)

def RestClear : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (LL : Formalism.GM.M.Letters N) (q : ℕ) (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ), ∀ F ∈ Formalism.GM.M.Y p (r := r) LL J M,
      ∃ e : ℕ, ((p : ℚ_[p]) ^ e) • F ∈ Formalism.GM.M.YZ p (r := r) LL J M

theorem restClear_proved : RestClear := by
  intro p _ N r _ LL q J M F hF
  classical
  obtain ⟨e, he⟩ : ∃ e : ℕ, ∀ m, ‖(p : ℚ_[p]) ^ e * F.coeff m‖ ≤ 1 := by
    set B : ℝ := ∑ m ∈ F.support, ‖F.coeff m‖ with hB
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    obtain ⟨e, he⟩ := pow_unbounded_of_one_lt B hp1
    refine ⟨e, fun m => ?_⟩
    rw [norm_mul, Padic.norm_p_pow]
    have hcm : ‖F.coeff m‖ ≤ B := by
      by_cases hm : m ∈ F.support
      · exact Finset.single_le_sum (f := fun m => ‖F.coeff m‖) (fun _ _ => norm_nonneg _) hm
      · rw [MvPolynomial.notMem_support_iff.1 hm, norm_zero]
        exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hp0 : (0 : ℝ) < (p : ℝ) ^ e := by positivity
    rw [zpow_neg, zpow_natCast, inv_mul_le_iff₀ hp0, mul_one]
    linarith
  refine ⟨e, ?_⟩
  have hY : ((p : ℚ_[p]) ^ e) • F ∈ Formalism.GM.M.Y p (r := r) LL J M := Submodule.smul_mem _ _ hF
  have hPol : ((p : ℚ_[p]) ^ e) • F ∈ Formalism.GM.M.Pol p r LL := (Submodule.mem_inf.1 hY).1
  have hInt : ((p : ℚ_[p]) ^ e) • F ∈ Formalism.GM.M.IntPol p (Fin N × Fin r) := by
    have hr : ((p : ℚ_[p]) ^ e) • F ∈ Set.range (MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p])) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro c hc
      obtain ⟨m, -, rfl⟩ : ∃ m ∈ (((p : ℚ_[p]) ^ e) • F).support, c = (((p : ℚ_[p]) ^ e) • F).coeff m := by
        simpa [MvPolynomial.coeffs, eq_comm] using hc
      rw [MvPolynomial.coeff_smul, smul_eq_mul]
      exact ⟨⟨_, he m⟩, rfl⟩
    obtain ⟨G, hG⟩ := hr
    exact ⟨G, hG⟩
  exact Submodule.mem_inf.2 ⟨hY, Submodule.mem_inf.2 ⟨hPol, hInt⟩⟩

theorem restYbc_of (hF : RestFunY) (hD : RestDecomp) (hC : RestClear) : RestYbc := by
  intro O _ _ p _ ι N r _ LL q J M y hy
  have hyK : y ∈ Yjt (KK O) (r := r) LL J M := hy.1
  obtain ⟨n, b, f, hf, hdec⟩ := hD O p ι _ y
  rw [hdec]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
  have h1 := hF O p ι N r LL q J M (f k) (hf k) y hyK
  obtain ⟨e, he⟩ := hC p N r (gmL LL) q J M _ h1
  have hp0 : ((p : ℚ_[p]) ^ e) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have e1 : map ι (cmap (f k) y) = (ι ((p : ℚ_[p]) ^ e))⁻¹ • map ι (((p : ℚ_[p]) ^ e) • cmap (f k) y) := by
    rw [MvPolynomial.smul_eq_C_mul (a := (ι ((p : ℚ_[p]) ^ e))⁻¹), MvPolynomial.smul_eq_C_mul (a := (p : ℚ_[p]) ^ e), map_mul,
      map_C, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ((map_ne_zero ι).2 hp0), C_1, one_mul]
  rw [e1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, he, rfl⟩)

theorem coeff_cmap {K L σ : Type} [CommRing K] [CommRing L] (f : K →+ L) (y : MvPolynomial σ K) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (cmap f y) m = f (y.coeff m) := by
  classical
  unfold cmap
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, map_zero]

theorem restDecomp_proved : RestDecomp := by
  intro O _ _ p _ ι σ y
  classical
  letI : Algebra ℚ_[p] (KK O) := ι.toAlgebra
  let V : Submodule ℚ_[p] (KK O) := Submodule.span ℚ_[p] (y.coeffs : Set (KK O))
  let bV := Module.finBasis ℚ_[p] V
  obtain ⟨rV, hrV⟩ := LinearMap.exists_leftInverse_of_injective V.subtype V.ker_subtype
  refine ⟨Module.finrank ℚ_[p] V, fun k => (bV k : KK O),
    fun k => ((bV.coord k).comp rV).toAddMonoidHom, ?_, ?_⟩
  · intro k a x
    have hx : ι a * x = a • x := by rw [Algebra.smul_def]; rfl
    show ((bV.coord k).comp rV) (ι a * x) = a * ((bV.coord k).comp rV) x
    rw [hx, map_smul, smul_eq_mul]
  · ext m
    have hc : y.coeff m ∈ V := by
      by_cases h0 : y.coeff m = 0
      · rw [h0]; exact V.zero_mem
      · exact Submodule.subset_span (MvPolynomial.coeff_mem_coeffs _ h0)
    have hrc : rV (y.coeff m) = ⟨y.coeff m, hc⟩ := by
      have := LinearMap.congr_fun hrV ⟨y.coeff m, hc⟩
      simpa using this
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, coeff_cmap, smul_eq_mul]
    have hsum := congrArg Subtype.val (bV.sum_repr ⟨y.coeff m, hc⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    conv_lhs => rw [← hsum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    show (bV.repr ⟨y.coeff m, hc⟩ k) • (bV k : KK O) = (bV k : KK O) * ι ((bV.coord k) (rV (y.coeff m)))
    rw [hrc, Module.Basis.coord_apply, Algebra.smul_def, mul_comm]
    rfl

theorem restYbc_of_funY (hF : RestFunY) : RestYbc := restYbc_of hF restDecomp_proved restClear_proved

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Fibre

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)


open Classical in
def Wl (dl : DCl X) (l : Fin X.s) : Finset ℕ :=
  X.winA.filter fun x => ∑ c, dl.2 l c ≤ x ∧ (X.S C0 CE1 CE2).P X.p l ∣ x - ∑ c, dl.2 l c

theorem topA_eq (dl : DCl X) (l : Fin X.s) : topA C0 CE1 CE2 X dl l = (Wl C0 CE1 CE2 X dl l).sup id := rfl

private theorem mem_Wl_iff_mem_winA_and_dvd_sub (dl : DCl X) (l : Fin X.s) (v : ℕ) :
    v ∈ Wl C0 CE1 CE2 X dl l ↔
      v ∈ X.winA ∧ (∑ c, dl.2 l c ≤ v ∧ (X.S C0 CE1 CE2).P X.p l ∣ v - ∑ c, dl.2 l c) := by
  unfold Wl
  rw [Finset.mem_filter]

private theorem mem_cbox_iff_mem_piFinset_and_compat (dl : DCl X) (a : Fin X.s → ℕ) :
    a ∈ cbox C0 CE1 CE2 X dl ↔ a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA) ∧ Compat C0 CE1 CE2 X dl a := by
  classical
  unfold cbox
  simp only [Finset.mem_filter]

theorem cbox_eq (dl : DCl X) (a0 : Fin X.s → ℕ) (h0 : a0 ∈ cbox C0 CE1 CE2 X dl) :
    cbox C0 CE1 CE2 X dl = Fintype.piFinset (Wl C0 CE1 CE2 X dl) := by
  have h0' := ((mem_cbox_iff_mem_piFinset_and_compat C0 CE1 CE2 X dl a0).1 h0).2
  simp only [Compat, DigitsOK, ColumnSystems.digitBlock] at h0'
  ext a
  rw [mem_cbox_iff_mem_piFinset_and_compat, Fintype.mem_piFinset, Fintype.mem_piFinset]
  simp only [Compat, DigitsOK, ColumnSystems.digitBlock, mem_Wl_iff_mem_winA_and_dvd_sub]
  constructor
  · rintro ⟨ha, -, -, h3⟩ i
    exact ⟨ha i, h3 i⟩
  · intro h
    exact ⟨fun i => (h i).1, h0'.1, h0'.2.1, fun i => (h i).2⟩

def cm (dl : DCl X) (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t) (v : ℕ) : ℕ :=
  (v - ∑ c, dl.2 (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) - x.1 i

def Nl (dl : DCl X) (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t) : Finset ℕ :=
  (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).image (cm C0 CE1 CE2 X dl x i)

theorem twoPow_pos (l : Fin X.s) : 0 < (X.S C0 CE1 CE2).P X.p l := by
  unfold SegData.P
  exact pow_pos X.std.1.prime.pos _

def LvlRoom (dl : DCl X) (x : Lv C0 CE1 CE2 X) : Prop :=
  ∀ i, ∀ v ∈ Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i),
    x.1 i ≤ (v - ∑ c, dl.2 (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i)

variable {C0 CE1 CE2 X}

theorem cm_inj {dl : DCl X} {x : Lv C0 CE1 CE2 X} (hr : LvlRoom C0 CE1 CE2 X dl x) (i : Fin (X.S C0 CE1 CE2).t) :
    Set.InjOn (cm C0 CE1 CE2 X dl x i) (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)) := by
  intro v hv v' hv' he
  have r1 := hr i v hv
  have r2 := hr i v' hv'
  simp only [Finset.mem_coe, mem_Wl_iff_mem_winA_and_dvd_sub] at hv hv'
  simp only [cm] at he
  have hPp := twoPow_pos C0 CE1 CE2 X (uTop (X.S C0 CE1 CE2) i)
  obtain ⟨k, hk⟩ := hv.2.2
  obtain ⟨k', hk'⟩ := hv'.2.2
  rw [hk, Nat.mul_div_cancel_left _ hPp] at r1
  rw [hk, Nat.mul_div_cancel_left _ hPp] at he
  rw [hk', Nat.mul_div_cancel_left _ hPp] at r2
  rw [hk', Nat.mul_div_cancel_left _ hPp] at he
  have hkk : k = k' := by omega
  subst hkk
  omega

theorem cm_mono (dl : DCl X) (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t) {v v' : ℕ} (h : v ≤ v') :
    cm C0 CE1 CE2 X dl x i v ≤ cm C0 CE1 CE2 X dl x i v' := by
  unfold cm
  exact Nat.sub_le_sub_right (Nat.div_le_div_right (Nat.sub_le_sub_right h _)) _

theorem Nl_conv {dl : DCl X} {x : Lv C0 CE1 CE2 X} (hr : LvlRoom C0 CE1 CE2 X dl x) (i : Fin (X.S C0 CE1 CE2).t) :
    ∀ y ∈ Nl C0 CE1 CE2 X dl x i, ∀ y' ∈ Nl C0 CE1 CE2 X dl x i, ∀ z, y ≤ z → z ≤ y' → z ∈ Nl C0 CE1 CE2 X dl x i := by
  intro y hy y' hy' z hyz hzy'
  simp only [Nl, Finset.mem_image] at hy hy' ⊢
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨v', hv', rfl⟩ := hy'
  have r1 := hr i v hv
  have r2 := hr i v' hv'
  simp only [mem_Wl_iff_mem_winA_and_dvd_sub, Formalism.MainNotions.flipOneThree.Inst.winA, Finset.mem_Icc] at hv hv' ⊢
  simp only [cm] at hyz hzy' ⊢
  have hPp := twoPow_pos C0 CE1 CE2 X (uTop (X.S C0 CE1 CE2) i)
  obtain ⟨k, hk⟩ := hv.2.2
  obtain ⟨k', hk'⟩ := hv'.2.2
  rw [hk, Nat.mul_div_cancel_left _ hPp] at r1
  rw [hk, Nat.mul_div_cancel_left _ hPp] at hyz
  rw [hk', Nat.mul_div_cancel_left _ hPp] at r2
  rw [hk', Nat.mul_div_cancel_left _ hPp] at hzy'
  have hle1 : k ≤ z + x.1 i := by omega
  have hle2 : z + x.1 i ≤ k' := by omega
  have m1 := Nat.mul_le_mul_left ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i)) hle1
  have m2 := Nat.mul_le_mul_left ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i)) hle2
  refine ⟨(∑ c, dl.2 (uTop (X.S C0 CE1 CE2) i) c) + (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) * (z + x.1 i), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · omega
  · omega
  · omega
  · exact ⟨z + x.1 i, by omega⟩
  · rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hPp, Nat.add_sub_cancel]

theorem cm_top {dl : DCl X} (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t)
    (hne : (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).Nonempty) :
    cm C0 CE1 CE2 X dl x i (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)) = (Nl C0 CE1 CE2 X dl x i).sup id := by
  rw [topA_eq]
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image _ id hne
  have hsup : (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).sup id = m :=
    le_antisymm (Finset.sup_le fun v hv => hmax v hv) (Finset.le_sup (f := id) hm)
  rw [hsup]
  apply le_antisymm
  · exact Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hm)
  · apply Finset.sup_le
    intro y hy
    simp only [Nl, Finset.mem_image] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    exact cm_mono dl x i (hmax v hv)

variable (C0 CE1 CE2 X)

def XMof (dl : DCl X) (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) : flipOneThree.InstM where
  p := X.p
  hp := X.std.1.prime
  s := X.s
  r := X.r
  hr := X.hm
  LL := lLL C0 CE1 CE2 X a b x
  T := gT C0 CE1 CE2 X b
  a := X.L.a
  E := X.L.Y * kapS X
  Yl := fun i => (Nl C0 CE1 CE2 X dl x i).sup id - sInf ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ) + 1
  n₀ := fun i => sInf ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ)
  dd := fun _ => 1
  ρ := ⟨X.r - 1, Nat.sub_lt (Nat.pos_of_ne_zero X.hm) one_pos⟩

def BADf (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) (D : ℤ) (n : Fin (X.S C0 CE1 CE2).t → ℕ) : ℕ :=
  Formalism.GM.M.bad X.p (fun F G => Formalism.GM.M.fockN X.p ((lLL C0 CE1 CE2 X a b x).setTies (gT C0 CE1 CE2 X b) n)
            ((gT C0 CE1 CE2 X b).phis X.p (r := X.r) ((lLL C0 CE1 CE2 X a b x).setTies (gT C0 CE1 CE2 X b) n) F) G)
    (Formalism.GM.M.YZ X.p (r := X.r) ((lLL C0 CE1 CE2 X a b x).setTies (gT C0 CE1 CE2 X b) n) (gT C0 CE1 CE2 X b).J
      (gT C0 CE1 CE2 X b).thr) D

def FRf (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) (n : Fin (X.S C0 CE1 CE2).t → ℕ) : ℕ :=
  Module.finrank ℚ_[X.p] (Formalism.GM.M.Y X.p (r := X.r) ((lLL C0 CE1 CE2 X a b x).setTies (gT C0 CE1 CE2 X b) n)
    (gT C0 CE1 CE2 X b).J (gT C0 CE1 CE2 X b).thr)

theorem bY_ovr (dl : DCl X) (a : Fin X.s → ℕ) (n : Fin (X.S C0 CE1 CE2).t → ℕ) (b : SegBlock X.s X.r)
    (hb : b.ry = dl.2) (x : Lv C0 CE1 CE2 X) (D : ℤ) :
    bY C0 CE1 CE2 X (ovr (uTop (X.S C0 CE1 CE2)) a n) b x D =
      BADf C0 CE1 CE2 X a b x D (fun i => cm C0 CE1 CE2 X dl x i (n i)) := by
  have h := lLL_ovr C0 CE1 CE2 X a n b x
  have hf : (fun i => cm C0 CE1 CE2 X dl x i (n i)) = (fun i : Fin (X.S C0 CE1 CE2).t =>
      (n i - ∑ c, b.ry (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) - x.1 i) := by
    funext i
    simp only [cm, hb]
  unfold BADf bY badY
  rw [hf, ← h]
  rfl

theorem dimY_ovr (dl : DCl X) (a : Fin X.s → ℕ) (n : Fin (X.S C0 CE1 CE2).t → ℕ) (b : SegBlock X.s X.r)
    (hb : b.ry = dl.2) (x : Lv C0 CE1 CE2 X) :
    dimY X.p (r := X.r) (gB C0 CE1 CE2 X (ovr (uTop (X.S C0 CE1 CE2)) a n) 0 b) x.1 x.2 =
      FRf C0 CE1 CE2 X a b x (fun i => cm C0 CE1 CE2 X dl x i (n i)) := by
  have h := lLL_ovr C0 CE1 CE2 X a n b x
  have hf : (fun i => cm C0 CE1 CE2 X dl x i (n i)) = (fun i : Fin (X.S C0 CE1 CE2).t =>
      (n i - ∑ c, b.ry (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) - x.1 i) := by
    funext i
    simp only [cm, hb]
  unfold FRf dimY
  rw [hf, ← h]
  rfl

end Fibre

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
