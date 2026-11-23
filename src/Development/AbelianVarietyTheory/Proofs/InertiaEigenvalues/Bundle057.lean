module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

open Matrix MeasureTheory Filter Topology in
private theorem addChar_dotProduct_eq_one_of_norm_le {F : Type} [NontriviallyNormedField F]
    [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : _root_.GlobalTheory.JR.IsStdChar ψ) {r : ℕ}
    {R : ℝ} (x δ : Fin r → F) (hx : ‖x‖ ≤ R) (hδ : ‖δ‖ * R ≤ 1) : ψ (x ⬝ᵥ δ) = 1 := by
  apply hψ.1
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [norm_mul]
  calc ‖x i‖ * ‖δ i‖ ≤ R * ‖δ‖ :=
        mul_le_mul ((norm_le_pi_norm x i).trans hx) (norm_le_pi_norm δ i) (norm_nonneg _)
          ((norm_nonneg _).trans hx)
    _ = ‖δ‖ * R := mul_comm _ _
    _ ≤ 1 := hδ


open Matrix MeasureTheory Filter Topology in
theorem _root_.GlobalTheory.JR.fourG_isLocallyConstant_of_invariant :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      [_root_.GlobalTheory.JR.Unram F E] (r : ℕ) (M : _root_.GlobalTheory.JR.Meas r F E) (ψ : AddChar F ℂ),
      _root_.GlobalTheory.JR.IsStdChar ψ → ∀ f' : _root_.GlobalTheory.JR.Gl r F → ℂ, _root_.GlobalTheory.JR.IsTest f' →
      (∃ U ∈ 𝓝 (0 : _root_.GlobalTheory.JR.Gl r F), ∀ Y : _root_.GlobalTheory.JR.Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y) →
      IsLocallyConstant (_root_.GlobalTheory.JR.fourG M ψ f') := by
  intro F E _ _ _ _ _ r M ψ hψ f hf ⟨U, hU, hUf⟩
  haveI := _root_.GlobalTheory.JR.Unram.ultraF (F := F) E
  obtain ⟨C, hC⟩ := hf.2.isCompact.exists_bound_of_continuousOn
    (f := fun x : _root_.GlobalTheory.JR.Gl r F => (x.2.1, x.2.2.1))
    (continuous_snd.fst.prodMk continuous_snd.snd.fst).continuousOn
  set R : ℝ := |C| + 1 with hRdef
  have hRpos : 0 < R := by positivity
  have hCR : C ≤ R := (le_abs_self C).trans (by rw [hRdef]; linarith)
  have hbd : ∀ x ∈ tsupport f, ‖x.2.1‖ ≤ R ∧ ‖x.2.2.1‖ ≤ R := by
    intro x hx
    have h : ‖(x.2.1, x.2.2.1)‖ ≤ C := hC x hx
    exact ⟨(norm_fst_le (x.2.1, x.2.2.1)).trans (h.trans hCR),
      (norm_snd_le (x.2.1, x.2.2.1)).trans (h.trans hCR)⟩
  let P : _root_.GlobalTheory.JR.Gl r F → _root_.GlobalTheory.JR.Gl r F := fun u => (u.1, 0, 0, u.2.2.2)
  have hP : Continuous P :=
    continuous_fst.prodMk (continuous_const.prodMk (continuous_const.prodMk continuous_snd.snd.snd))
  have hP0 : P 0 = 0 := rfl
  set W : Set (_root_.GlobalTheory.JR.Gl r F) :=
    P ⁻¹' U ∩ {u | ‖u.2.1‖ < R⁻¹} ∩ {u | ‖u.2.2.1‖ < R⁻¹} with hWdef
  have hW : W ∈ 𝓝 (0 : _root_.GlobalTheory.JR.Gl r F) := by
    refine inter_mem (inter_mem (hP.continuousAt.preimage_mem_nhds (by rwa [hP0])) ?_) ?_
    · exact (isOpen_lt (continuous_norm.comp continuous_snd.fst) continuous_const).mem_nhds
        (by simp [hRpos])
    · exact (isOpen_lt (continuous_norm.comp continuous_snd.snd.fst) continuous_const).mem_nhds
        (by simp [hRpos])
  rw [IsLocallyConstant.iff_eventually_eq]
  intro Y
  have hnb : {Y' | Y' - Y ∈ W} ∈ 𝓝 Y :=
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using hW)
  filter_upwards [hnb] with Y' hY'
  obtain ⟨⟨hu1, hu2⟩, hu3⟩ := hY'
  obtain ⟨u, rfl⟩ : ∃ u, Y' = Y + u := ⟨Y' - Y, by abel⟩
  simp only [add_sub_cancel_left] at hu1 hu2 hu3
  unfold _root_.GlobalTheory.JR.fourG
  congr 1; funext b'; congr 1; funext c'
  have hfeq : f ((Y + u).1, b', c', (Y + u).2.2.2) = f (Y.1, b', c', Y.2.2.2) := by
    have := hUf (Y.1, b', c', Y.2.2.2) (P u) hu1
    convert this using 2
    ext <;> simp [P]
  rw [hfeq]
  by_cases h0 : f (Y.1, b', c', Y.2.2.2) = 0
  · simp [h0]
  have hmem : (Y.1, b', c', Y.2.2.2) ∈ tsupport f := subset_tsupport f h0
  obtain ⟨hb', hc'⟩ := hbd _ hmem
  have e1 : ψ (c' ⬝ᵥ u.2.1) = 1 := addChar_dotProduct_eq_one_of_norm_le hψ c' u.2.1 hc'
    (by rw [← le_div_iff₀ hRpos, one_div]; exact hu2.le)
  have e2 : ψ (u.2.2.1 ⬝ᵥ b') = 1 := by
    rw [dotProduct_comm]
    exact addChar_dotProduct_eq_one_of_norm_le hψ b' u.2.2.1 hb'
      (by rw [← le_div_iff₀ hRpos, one_div]; exact hu3.le)
  have hsum : c' ⬝ᵥ (Y + u).2.1 + (Y + u).2.2.1 ⬝ᵥ b' =
      (c' ⬝ᵥ Y.2.1 + Y.2.2.1 ⬝ᵥ b') + c' ⬝ᵥ u.2.1 + u.2.2.1 ⬝ᵥ b' := by
    simp only [Prod.snd_add, Prod.fst_add, dotProduct_add, add_dotProduct]
    abel
  rw [hsum, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, e1, e2, mul_one, mul_one]

end GlobalTheory.JR
end

section

open Matrix

noncomputable section

namespace GlobalTheory.JR.Step

section Alg
variable {r : ℕ} {k : Type} [CommRing k]

def eL (r : ℕ) (k : Type) [CommRing k] : Fin (r + 1) → k := Pi.single (Fin.last r) 1

def blocks (A : Matrix (Fin (r + 1)) (Fin (r + 1)) k) : Gl r k :=
  (A.submatrix Fin.castSucc Fin.castSucc, fun i => A (Fin.castSucc i) (Fin.last r),
    fun j => A (Fin.last r) (Fin.castSucc j), A (Fin.last r) (Fin.last r))

def lift (Z : Gl r k) (μ l : k) : Gl (r + 1) k := (full Z, μ • eL r k, eL r k, l)

def embHom (r : ℕ) (k : Type) [CommRing k] :
    Matrix (Fin r) (Fin r) k →* Matrix (Fin (r + 1)) (Fin (r + 1)) k where
  toFun g := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 1)
  map_one' := by
    rw [Matrix.fromBlocks_one]
    exact Matrix.submatrix_one_equiv _
  map_mul' g h := by
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

def emb (r : ℕ) (k : Type) [CommRing k] : GL (Fin r) k →* GL (Fin (r + 1)) k := Units.map (embHom r k)

def glMap {k' : Type} [CommRing k'] (φ : k →+* k') (Y : Gl r k) : Gl r k' :=
  (Y.1.map φ, fun i => φ (Y.2.1 i), fun i => φ (Y.2.2.1 i), φ Y.2.2.2)

end Alg

section Herm
variable {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]

theorem full_toGl_isSelfAdjoint (X : Hn r F E) (hl : star (algebraMap F E X.2.2) = algebraMap F E X.2.2) :
    IsSelfAdjoint (full X.toGl) := by
  have hA : X.1.1ᴴ = X.1.1 := X.1.2
  unfold IsSelfAdjoint full Hn.toGl
  simp only [Matrix.star_eq_conjTranspose, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.fromBlocks_conjTranspose, hA]
  congr 1
  congr 1
  all_goals (ext i j; simp [hl])

end Herm

section Unr
variable {r : ℕ} {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
  [StarRing E] [Unram F E]

def liftH (X : Hn r F E) (ν : E) (l : F) : Hn (r + 1) F E :=
  (⟨full X.toGl, full_toGl_isSelfAdjoint X (Unram.star_fix _)⟩, ν • eL r E, l)

def uEmb (r : ℕ) (E : Type) [Field E] [StarRing E] :
    Matrix.unitaryGroup (Fin r) E →* Matrix.unitaryGroup (Fin (r + 1)) E where
  toFun g := ⟨embHom r E g.1, by
    have hs : star (embHom r E g.1) = embHom r E (star g.1) := by
      simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.star_eq_conjTranspose, Matrix.reindex_apply,
        Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
        Matrix.conjTranspose_one]
    rw [Matrix.mem_unitaryGroup_iff, hs, ← map_mul, Matrix.mem_unitaryGroup_iff.mp g.2, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ _ _)

end Unr

end GlobalTheory.JR.Step
end
end

section

open GlobalTheory.PMonE

namespace GlobalTheory.PMonE

open Finset

theorem norm_det_le_one_of_entries {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    [DecidableEq m] (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) : ‖A.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [norm_mul, norm_prod]
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : F)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hs, one_mul]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hA _ _)

theorem norm_adjugate_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    [DecidableEq m] (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (i j : m) : ‖A.adjugate i j‖ ≤ 1 := by
  rw [Matrix.adjugate_apply]
  refine norm_det_le_one_of_entries _ fun a b => ?_
  by_cases h : a = j
  · subst h
    rw [Matrix.updateRow_self]
    by_cases hb : b = i
    · subst hb; simp
    · simp [Pi.single_apply, hb]
  · rw [Matrix.updateRow_ne h]; exact hA a b

theorem norm_inv_le_one_of_det {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    [DecidableEq m] (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hd : ‖A.det‖ = 1) (i j : m) :
    ‖A⁻¹ i j‖ ≤ 1 := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, hd, inv_one, one_mul]
  exact norm_adjugate_le_one A hA i j

theorem norm_mul_apply_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    (A B : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1) (i j : m) :
    ‖(A * B) i j‖ ≤ 1 := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hB k j)

theorem norm_mul_apply_lt_one {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    (A B : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ < 1) (i j : m) :
    ‖(A * B) i j‖ < 1 := by
  rw [Matrix.mul_apply]
  rcases isEmpty_or_nonempty m with hm | hm
  · simp
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image (univ : Finset m) (fun k => ‖A i k * B k j‖) univ_nonempty
  have hlt : ‖A i k₀ * B k₀ j‖ < 1 := by
    rw [norm_mul]
    calc ‖A i k₀‖ * ‖B k₀ j‖ ≤ 1 * ‖B k₀ j‖ := mul_le_mul_of_nonneg_right (hA i k₀) (norm_nonneg _)
      _ = ‖B k₀ j‖ := one_mul _
      _ < 1 := hB k₀ j
  exact lt_of_le_of_lt
    (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k hk => hk₀ k hk) hlt

theorem normal_of_inv_mul : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (m : Type) [Fintype m]
    [DecidableEq m] (N : ℕ) (B : ℕ → Matrix m m F), (∀ n i j, ‖B n i j‖ ≤ 1) →
    (∀ n, N < n → ∀ i j, ‖B n i j‖ < 1) → ‖(B N).det‖ = 1 →
    Normal N (fun n => (B N)⁻¹ * B n) ∧ ∀ i j, ‖(B N)⁻¹ i j‖ ≤ 1 := by
  intro F _ _ m _ _ N B hint hsmall hd
  have hinv : ∀ i j, ‖(B N)⁻¹ i j‖ ≤ 1 := norm_inv_le_one_of_det (B N) (hint N) hd
  have hunit : IsUnit (B N).det := by
    rw [isUnit_iff_ne_zero]; intro h0; rw [h0, norm_zero] at hd; exact zero_ne_one hd
  refine ⟨⟨fun n i j => norm_mul_apply_le_one _ _ hinv (hint n) i j, ?_,
    fun n hn i j => norm_mul_apply_lt_one _ _ hinv (hsmall n hn) i j⟩, hinv⟩
  exact Matrix.nonsing_inv_mul _ hunit

end GlobalTheory.PMonE
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem slices_test {P V Q : Type} [TopologicalSpace P] [TopologicalSpace V] [TopologicalSpace Q] [T2Space P]
    [T2Space V] [T2Space Q] (T : (V → ℂ) → V → ℂ) (hT : ∀ φ, IsTest φ → IsTest (T φ)) (hT0 : T 0 = 0)
    (f : P × V × Q → ℂ) (hf : IsTest f) :
    (∀ p q, IsTest (fun v => f (p, v, q))) ∧
      IsTest (fun x : P × V × Q => T (fun v => f (x.1, v, x.2.2)) x.2.1) := by
  obtain ⟨hlc, hcs⟩ := hf
  have hC : IsCompact (tsupport f) := hcs
  have hz : ∀ x, x ∉ tsupport f → f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have h1 : ∀ p q, IsTest (fun v => f (p, v, q)) := by
    intro p q
    refine ⟨hlc.comp_continuous (by fun_prop), ?_⟩
    have hcl : IsClosed ({x : P × V × Q | x.1 = p} ∩ {x | x.2.2 = q}) :=
      (isClosed_eq continuous_fst continuous_const).inter
        (isClosed_eq (continuous_snd.comp continuous_snd) continuous_const)
    refine HasCompactSupport.intro ((hC.inter_right hcl).image (continuous_fst.comp continuous_snd)) ?_
    intro v hv
    apply hz
    intro hmem
    exact hv ⟨(p, v, q), ⟨hmem, rfl, rfl⟩, rfl⟩
  refine ⟨h1, ?_⟩
  set Φ : P × Q → V → ℂ := fun a v => f (a.1, v, a.2) with hΦdef
  set CV : Set V := (fun x : P × V × Q => x.2.1) '' tsupport f with hCV
  have hCVc : IsCompact CV := hC.image (continuous_fst.comp continuous_snd)
  have hoff : ∀ (a : P × Q) v, v ∉ CV → f (a.1, v, a.2) = 0 := by
    intro a v hv
    exact hz _ (fun h => hv ⟨_, h, rfl⟩)
  have hΦ : IsLocallyConstant Φ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro a0
    have hn : IsOpen {z : (P × Q) × V | f (z.1.1, z.2, z.1.2) = f (a0.1, z.2, a0.2)} := by
      have g1 : IsLocallyConstant (fun z : (P × Q) × V => f (z.1.1, z.2, z.1.2)) :=
        hlc.comp_continuous (by fun_prop)
      have g2 : IsLocallyConstant (fun z : (P × Q) × V => f (a0.1, z.2, a0.2)) :=
        hlc.comp_continuous (by fun_prop)
      refine isOpen_iff_mem_nhds.2 fun z hz' => ?_
      filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 g1 z, (IsLocallyConstant.iff_eventually_eq _).1 g2 z]
        with y hy1 hy2
      show f (y.1.1, y.2, y.1.2) = f (a0.1, y.2, a0.2)
      rw [hy1, hy2]
      exact hz'
    obtain ⟨u, w, hu, -, hau, hCVw, huw⟩ :=
      generalized_tube_lemma (isCompact_singleton (x := a0)) hCVc hn (by
        rintro ⟨a, v⟩ ⟨ha, -⟩
        rw [Set.mem_singleton_iff] at ha
        subst ha
        rfl)
    filter_upwards [hu.mem_nhds (hau rfl)] with a ha
    funext v
    by_cases hv : v ∈ CV
    · exact huw (show (a, v) ∈ u ×ˢ w from ⟨ha, hCVw hv⟩)
    · show f (a.1, v, a.2) = f (a0.1, v, a0.2)
      rw [hoff a v hv, hoff a0 v hv]
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x0
    have e1 : ∀ᶠ x in 𝓝 x0, Φ (x.1, x.2.2) = Φ (x0.1, x0.2.2) :=
      ((continuous_fst.prodMk (continuous_snd.comp continuous_snd)).tendsto x0).eventually
        ((IsLocallyConstant.iff_eventually_eq _).1 hΦ _)
    have e2 : ∀ᶠ x in 𝓝 x0, T (Φ (x0.1, x0.2.2)) x.2.1 = T (Φ (x0.1, x0.2.2)) x0.2.1 :=
      ((continuous_fst.comp continuous_snd).tendsto x0).eventually
        ((IsLocallyConstant.iff_eventually_eq _).1 (hT _ (h1 _ _)).1 _)
    filter_upwards [e1, e2] with x h h'
    show T (Φ (x.1, x.2.2)) x.2.1 = T (Φ (x0.1, x0.2.2)) x0.2.1
    rw [h]
    exact h'
  · set K : Set (P × Q) := (fun x : P × V × Q => (x.1, x.2.2)) '' tsupport f with hKdef
    have hK : IsCompact K := hC.image (by fun_prop)
    have hΦK : ∀ a, a ∉ K → Φ a = 0 := by
      intro a ha
      funext v
      exact hz _ (fun h => ha ⟨_, h, rfl⟩)
    haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
    have hfin : (Set.range (fun a : K => Φ a)).Finite :=
      (hΦ.comp_continuous continuous_subtype_val).range_finite
    set U : Set V := ⋃ h ∈ Set.range (fun a : K => Φ a), tsupport (T h) with hUdef
    have hU : IsCompact U := hfin.isCompact_biUnion (fun h hh => by
      obtain ⟨a, rfl⟩ := hh
      exact (hT _ (h1 _ _)).2.isCompact)
    have hL : IsCompact ((fun z : (P × Q) × V => (z.1.1, z.2, z.1.2)) '' (K ×ˢ U)) :=
      (hK.prod hU).image (by fun_prop)
    refine HasCompactSupport.intro hL ?_
    intro x hx
    by_contra hne
    apply hx
    have ha : (x.1, x.2.2) ∈ K := by
      by_contra hK'
      apply hne
      show T (Φ (x.1, x.2.2)) x.2.1 = 0
      rw [hΦK _ hK', hT0]
      rfl
    refine ⟨((x.1, x.2.2), x.2.1), ⟨ha, ?_⟩, rfl⟩
    exact Set.mem_biUnion ⟨⟨(x.1, x.2.2), ha⟩, rfl⟩ (subset_tsupport _ hne)

theorem slices_test' : ∀ {P V Q : Type} [TopologicalSpace P] [TopologicalSpace V] [TopologicalSpace Q] [T2Space P] [T2Space V] [T2Space Q] (T : (V → ℂ) → V → ℂ), (∀ φ, IsTest φ → IsTest (T φ)) → T 0 = 0 → ∀ f : P × V × Q → ℂ, IsTest f → (∀ p q, IsTest (fun v => f (p, v, q))) ∧ IsTest (fun x : P × V × Q => T (fun v => f (x.1, v, x.2.2)) x.2.1) :=
  fun T hT hT0 f hf => slices_test T hT hT0 f hf

end GlobalTheory
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.UnitTest

theorem isLocallyConstant_indicator_one {Z : Type} [TopologicalSpace Z] {W : Set Z} (hW : IsClopen W) :
    IsLocallyConstant (W.indicator (1 : Z → ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ W
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem unitG_isTest (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
    (r : ℕ) : IsTest (unitG r F) := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  set B : Set F := Metric.closedBall 0 1 with hB
  have hBo : IsOpen B := IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hBc : IsClosed B := Metric.isClosed_closedBall
  have hBk : IsCompact B := isCompact_closedBall 0 1
  set A : Set (Matrix (Fin r) (Fin r) F) := Set.univ.pi fun _ => Set.univ.pi fun _ => B with hA
  set V : Set (Fin r → F) := Set.univ.pi fun _ => B with hV
  have hVo : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => hBo
  have hVc : IsClosed V := isClosed_set_pi fun _ _ => hBc
  have hVk : IsCompact V := isCompact_univ_pi fun _ => hBk
  have hAo : IsOpen A := isOpen_set_pi Set.finite_univ fun _ _ => hVo
  have hAc : IsClosed A := isClosed_set_pi fun _ _ => hVc
  have hAk : IsCompact A := isCompact_univ_pi (X := fun _ : Fin r => Fin r → F) fun _ => hVk
  set S : Set (Gl r F) := A ×ˢ (V ×ˢ (V ×ˢ B)) with hS
  have hSeq : {Y : Gl r F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1}
      = S := by
    ext Y
    rw [Set.mem_setOf_eq, hS, hA, hV, hB]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun i _ j _ => ?_, fun i _ => ?_, fun i _ => ?_, ?_⟩
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h1 i j
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h2 i
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h3 i
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h4
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun i j => ?_, fun i => ?_, fun i => ?_, ?_⟩
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h1 i trivial j trivial
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h2 i trivial
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h3 i trivial
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h4
  have hSo : IsOpen S := hAo.prod (hVo.prod (hVo.prod hBo))
  have hSc : IsClosed S := hAc.prod (hVc.prod (hVc.prod hBc))
  have hSk : IsCompact S := hAk.prod (hVk.prod (hVk.prod hBk))
  unfold unitG
  rw [hSeq]
  exact ⟨isLocallyConstant_indicator_one ⟨hSc, hSo⟩,
    HasCompactSupport.intro' hSk hSc fun x hx => Set.indicator_of_notMem hx _⟩

end GlobalTheory.JR.UnitTest
end

section

open GlobalTheory.PMonE

namespace GlobalTheory.PMonE

theorem iter_frobSymm_pow {F : Type*} [CommRing F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (m : ℕ) (y : F) : (((frobeniusEquiv F p).symm)^[m] y) ^ p ^ m = y := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih, frobeniusEquiv_symm_pow_p]

theorem norm_pw_mono {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (k : ℤ) (y y' : F) (hy : ‖y‖ ≤ ‖y'‖) : ‖pw p k y‖ ≤ ‖pw p k y'‖ := by
  unfold pw
  split_ifs with hk
  · rw [norm_pow, norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hy _
  · set m := (-k).toNat
    have hN : p ^ m ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
    have e1 := iter_frobSymm_pow p m y
    have e2 := iter_frobSymm_pow p m y'
    by_contra hc
    push_neg at hc
    have := pow_lt_pow_left₀ hc (norm_nonneg _) hN
    rw [← norm_pow, ← norm_pow, e1, e2] at this
    linarith

theorem term_norm_mono : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π x : Fin h → F), (∀ j, ‖x j‖ ≤ ‖π j‖) → ∀ (r j : Fin h) (n : ℤ), ‖term p ϖ lam x r j n‖ ≤ ‖term p ϖ lam π r j n‖ := by
  intro F _ p _ _ _ h ϖ lam π x hx r j n
  unfold term
  rw [norm_mul, norm_mul (lam j * _)]
  exact mul_le_mul_of_nonneg_left (norm_pw_mono p _ _ _ (hx j)) (norm_nonneg _)

end GlobalTheory.PMonE
end
