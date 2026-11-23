module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle541
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import GroundTheory.AutomorphicForms.Bundle012
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import GroundTheory.LocalFields.LocalFourierHaar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle542
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def OffPl {S T' : HSp D} (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (u : WO S T') : Prop :=
  u.map (infPart D) = 0 ∧
    ∀ v ∈ Sb, ∀ ε, IsPlaceIdem D v ε → ∀ i j, algebraMap (AF D.host.F) (AE D) ε * u i j = 0

def SuppIn (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (V : HSp D) (g : GA D V) : Prop :=
  (mt V g - 1).map (infPart D) = 0 ∧
    ∀ v, v ∉ Sb → ∀ ε, IsPlaceIdem D v ε → ∀ i j, algebraMap (AF D.host.F) (AE D) ε * (mt V g - 1) i j = 0

def Over (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal

def LikeOff (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ c : WO (Vc D i) (Wc D i) →₀ ℂ, (∀ u ∈ c.support, OffPl Sb u) →
    (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u (R.vP i t)) = 0 →
    (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u f) = 0

def TypeIn (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t), SuppIn Sb (Vc D i) κ →
    R.ωP i t (κ, 1) f = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • f

def CleanIn (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) →
    (∃ v ∈ Sb, Over PP.1 v) → ∀ κ : G → GA D (Vc D i), IsLifts R i t κ →
      (∀ g, mirC R i PP a tr ε g ≠ 0 → SuppIn Sb (Vc D i) (κ g)) → avgW R i t PP a tr ε κ f = 0

def StepGen (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    Set (WO (Vc D i) (Wc D i) → ℂ) :=
  {φ | ∃ (g : GA D (Wc D i)) (f : WO (Vc D i) (Wc D i) → ℂ),
    TypeIn R i t Sb f ∧ CleanIn R i t Sb f ∧ LikeOff R i t Sb f ∧ φ = R.ωP i t (1, g) f}


open Classical in
def dropPl (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  Sb.erase v

theorem dropPl_insert [DecidableEq (HeightOneSpectrum (𝓞 D.host.F))] {s : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ s) : dropPl (insert v s) v = s := by
  unfold dropPl
  convert Finset.erase_insert hv

end GlobalTheory.DownLift.GenFinite

end
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.ZUnfWt

open GlobalTheory.ZUnf

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem lastRow_mul_of_mem {h : GA E (m + 1)} (hh : h ∈ mirU (Ad E) (m + 1) m) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.lastRow (h * g) = GlobalTheory.ZEul.lastRow g := by
  funext j
  simp only [GlobalTheory.ZEul.lastRow, Units.val_mul, Matrix.mul_apply]
  rw [Finset.sum_eq_single (Fin.last m)]
  · rw [(mem_mirU_last.1 hh) (Fin.last m), if_pos rfl, one_mul]
  · intro l _ hl
    rw [(mem_mirU_last.1 hh) l, if_neg hl, zero_mul]
  · simp


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem det_blkU {R : Type} [CommRing R] {a k : ℕ} (y : UnipotentBlockColumnIndex a k k → R) : (blkU y : GL (Fin a) R).val.det = 1 := by
  have h := mem_mirU_zero.1 (blkU_mem_mirU 0 y)
  rw [Matrix.det_of_upperTriangular (fun i j hij => h.1 i j hij)]
  simp [h.2]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem detPow_blkU (x : ℝ) {k : ℕ} (y : UnipotentBlockColumnIndex (m + 1) k k → Ad E) : detPow E (m + 1) x (blkU y) = 1 := by
  have hd : Matrix.GeneralLinearGroup.det (blkU y : GA E (m + 1)) = 1 := Units.ext (det_blkU y)
  unfold detPow chiDet
  rw [MonoidHom.comp_apply, hd, map_one]
  simp


omit [_root_.NumberField.IsTotallyComplex E] in
theorem isClosed_natLat (N : ℕ) : IsClosed (natLat E N) := by
  haveI : T2Space (Af E) := inferInstanceAs (T2Space (RestrictedProduct _ _ _))
  have e : natLat E N = (fun z => (N : Af E) * z) '' (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  rw [e]
  exact ((GroundTheory.Global.isCompact_integralFiniteAdeles E).image (continuous_const.mul continuous_id)).isClosed

omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_yFin : Continuous (yFin (E := E) (m := m)) :=
  continuous_pi fun i => (continuous_snd : Continuous (GlobalTheory.RSJ.pFin E)).comp
    ((Units.continuous_val : Continuous fun g : GA E (m + 1) => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E))).matrix_elem
      (Fin.last m) i)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_detPow (x : ℝ) : Continuous (detPow E (m + 1) x) :=
  continuous_norm.comp (Units.continuous_val.comp
    ((GlobalTheory.HeckeGal.Model.absPow E x).2.1.comp Matrix.GeneralLinearGroup.continuous_det))

omit [_root_.NumberField.IsTotallyComplex E] in
theorem measurable_wt (N : ℕ) (x : ℝ) : Measurable (wt (E := E) (m := m) N x) := by
  let S : Set (Fin (m + 1) → Af E) := {y | ∀ i : Fin (m + 1), y i - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈ natLat E N}
  have hS : IsClosed S := by
    have e : S = ⋂ i : Fin (m + 1),
        (fun y : Fin (m + 1) → Af E => y i - (if (i : ℕ) + 1 = m + 1 then 1 else 0)) ⁻¹' natLat E N := by
      ext y; simp [S]
    rw [e]
    exact isClosed_iInter fun i => (isClosed_natLat N).preimage ((continuous_apply i).sub continuous_const)
  have hm : MeasurableSet {g : GA E (m + 1) | yFin g ∈ S} := (hS.preimage continuous_yFin).measurableSet
  have hind : Measurable fun g : GA E (m + 1) => indN N (yFin g) := by
    unfold indN
    exact Measurable.ite hm measurable_const measurable_const
  exact ((Complex.measurable_re.comp hind).mul (continuous_detPow x).measurable).real_toNNReal

theorem wt_measurable_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m N : ℕ) (x : ℝ),
    Measurable (GlobalTheory.ZUnf.wt (E := E) (m := m) N x) ∧
    (∀ γ ∈ mirU E (m + 1) m, ∀ g, GlobalTheory.ZUnf.wt N x (ratGL E (m + 1) γ * g) = GlobalTheory.ZUnf.wt N x g) ∧
    ∀ (k : ℕ) (y : UnipotentBlockColumnIndex (m + 1) k k → Ad E) (g : GA E (m + 1)), GlobalTheory.ZUnf.wt N x (blkU y * g) = GlobalTheory.ZUnf.wt N x g := by
  intro E _ _ _ m N x
  refine ⟨measurable_wt N x, fun γ hγ g => ?_, fun k y g => ?_⟩
  · refine wt_of_lastRow_of_detPow (lastRow_mul_of_mem (map_mem_mirU _ hγ) g) ?_
    rw [GlobalTheory.RSJ.Model.detPow_mul, GlobalTheory.RSJ.Model.detPow_ratGL, one_mul]
  · refine wt_of_lastRow_of_detPow (lastRow_mul_of_mem (blkU_mem_mirU m y) g) ?_
    rw [GlobalTheory.RSJ.Model.detPow_mul, detPow_blkU, one_mul]

end GlobalTheory.ZUnfWt
end
end

section

open scoped InnerProductSpace BigOperators

noncomputable section

namespace GlobalTheory.UpInj.LocalSum

def dc {Γ : Type} [Group Γ] (K : Subgroup Γ) (c : Γ →* Γ) (g : Γ) : Set Γ :=
  {y | ∃ k₁ k₂, k₁ ∈ K ∧ c k₁ = k₁ ∧ k₂ ∈ K ∧ c k₂ = k₂ ∧ y = k₁ * g * k₂}

theorem mem_dc_self {Γ : Type} [Group Γ] (K : Subgroup Γ) (c : Γ →* Γ) (g : Γ) : g ∈ dc K c g :=
  ⟨1, 1, K.one_mem, map_one c, K.one_mem, map_one c, by simp⟩

theorem mul_mem_dc {Γ : Type} [Group Γ] (K : Subgroup Γ) (c : Γ →* Γ) {g y k : Γ} (h : y ∈ dc K c g)
    (hk : k ∈ K) (hck : c k = k) : y * k ∈ dc K c g := by
  obtain ⟨k₁, k₂, h1, h2, h3, h4, rfl⟩ := h
  exact ⟨k₁, k₂ * k, h1, h2, K.mul_mem h3 hk, by rw [map_mul, h4, hck], by simp [mul_assoc]⟩

theorem dc_eq_of_mem {Γ : Type} [Group Γ] (K : Subgroup Γ) (c : Γ →* Γ) {g y : Γ} (h : y ∈ dc K c g) :
    dc K c y = dc K c g := by
  obtain ⟨k₁, k₂, h1, h2, h3, h4, rfl⟩ := h
  ext z
  constructor
  · rintro ⟨l₁, l₂, i1, i2, i3, i4, rfl⟩
    exact ⟨l₁ * k₁, k₂ * l₂, K.mul_mem i1 h1, by rw [map_mul, i2, h2], K.mul_mem h3 i3,
      by rw [map_mul, h4, i4], by simp [mul_assoc]⟩
  · rintro ⟨l₁, l₂, i1, i2, i3, i4, rfl⟩
    exact ⟨l₁ * k₁⁻¹, k₂⁻¹ * l₂, K.mul_mem i1 (K.inv_mem h1), by rw [map_mul, map_inv, i2, h2],
      K.mul_mem (K.inv_mem h3) i3, by rw [map_mul, map_inv, h4, i4], by group⟩

theorem out_mk {Γ : Type} [Group Γ] (K : Subgroup Γ) (c : Γ →* Γ) (δ : Γ) :
    ∃ h, c h ∈ K ∧ Quotient.out (QuotientGroup.mk δ : Γ ⧸ K.comap c) = δ * h := by
  have e := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk δ : Γ ⧸ K.comap c))
  refine ⟨δ⁻¹ * Quotient.out (QuotientGroup.mk δ : Γ ⧸ K.comap c), ?_, by group⟩
  have := (K.comap c).inv_mem e
  rw [mul_inv_rev, inv_inv] at this
  exact this

end GlobalTheory.UpInj.LocalSum


open GlobalTheory.UpInj.LocalSum in
theorem GlobalTheory.UpInj.localSum_hasSum : ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (c : Γ →* Γ) (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (a : Γ → ℂ) (B : Γ → (H →L[ℂ] H)) (S : ℝ), (∀ g, c (c g) = c g) → (∀ g k k', k ∈ K → k' ∈ K → a (k * g * k') = a g) → (∀ g k, k ∈ K → B (g * k) = B g) → (∀ g, ‖B g‖ ≤ 1) → (∀ C : Finset Γ, (∀ g ∈ C, c g = g ∧ g ∉ K) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ K → g = g') → ∑ g ∈ C, ‖a g‖ ≤ S) → (∀ α, c α = α → ∃ C, GlobalTheory.UpInj.DCRep c K α C) → (∀ α C, c α = α → GlobalTheory.UpInj.DCRep c K α C → ∀ γ, ∑ δ ∈ C, B (γ * δ) = B γ * ∑ δ ∈ C, B δ) → ∀ γ, HasSum (fun x : Γ ⧸ K.comap c => a (c (Quotient.out x)) • B (γ * c (Quotient.out x))) (B γ * ∑' x : Γ ⧸ K.comap c, a (c (Quotient.out x)) • B (c (Quotient.out x))) := by
  intro Γ _ K c H _ _ _ a B S hc ha hB hB1 hS hex hH γ
  classical
  let r : Γ ⧸ K.comap c → Γ := fun x => c (Quotient.out x)
  have hr_fix : ∀ x, c (r x) = r x := fun x => hc _
  have hr_eq : ∀ x x' : Γ ⧸ K.comap c, (r x)⁻¹ * r x' ∈ K ↔ x = x' := by
    intro x x'
    have e : (r x)⁻¹ * r x' = c ((Quotient.out x)⁻¹ * Quotient.out x') := by simp [r, map_mul, map_inv]
    rw [e, ← Subgroup.mem_comap, ← QuotientGroup.eq, QuotientGroup.out_eq', QuotientGroup.out_eq']
  have hr_one : ∀ x : Γ ⧸ K.comap c, r x ∈ K ↔ x = (QuotientGroup.mk 1 : Γ ⧸ K.comap c) := by
    intro x
    have key : (QuotientGroup.mk 1 : Γ ⧸ K.comap c) = QuotientGroup.mk (Quotient.out x) ↔
        1⁻¹ * Quotient.out x ∈ K.comap c := QuotientGroup.eq
    rw [QuotientGroup.out_eq', inv_one, one_mul, Subgroup.mem_comap] at key
    rw [eq_comm]; exact key.symm
  have ha1 : ∀ g, g ∈ K → a g = a 1 := fun g hg => by simpa using ha 1 g 1 hg K.one_mem
  have hsum : Summable (fun x : Γ ⧸ K.comap c => ‖a (r x)‖) := by
    refine summable_of_sum_le (c := ‖a 1‖ + S) (fun x => norm_nonneg _) (fun u => ?_)
    rw [← Finset.sum_filter_add_sum_filter_not u (fun x => x = (QuotientGroup.mk 1 : Γ ⧸ K.comap c))]
    gcongr ?_ + ?_
    · calc ∑ x ∈ u.filter (fun x => x = QuotientGroup.mk 1), ‖a (r x)‖
            ≤ ∑ x ∈ {(QuotientGroup.mk 1 : Γ ⧸ K.comap c)}, ‖a (r x)‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => by simp [(Finset.mem_filter.1 hx).2])
              (fun _ _ _ => norm_nonneg _)
        _ = ‖a 1‖ := by rw [Finset.sum_singleton, ha1 _ ((hr_one _).2 rfl)]
    · rw [← Finset.sum_image (f := fun g => ‖a g‖) (fun x _ x' _ h => (hr_eq x x').1 (by rw [h, inv_mul_cancel]; exact K.one_mem))]
      apply hS
      · intro g hg
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hg
        exact ⟨hr_fix x, fun h => (Finset.mem_filter.1 hx).2 ((hr_one x).1 h)⟩
      · intro g hg g' hg' h
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hg
        obtain ⟨x', _, rfl⟩ := Finset.mem_image.1 hg'
        rw [(hr_eq x x').1 h]
  have hnorm : ∀ g γ', ‖a g • B (γ' * g)‖ ≤ ‖a g‖ := fun g γ' => by
    rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (hB1 _)
  let F : Γ ⧸ K.comap c → (H →L[ℂ] H) := fun x => a (c (Quotient.out x)) • B (γ * c (Quotient.out x))
  let G : Γ ⧸ K.comap c → (H →L[ℂ] H) := fun x => a (c (Quotient.out x)) • B (c (Quotient.out x))
  have hF : Summable F := Summable.of_norm_bounded hsum (fun x => hnorm _ _)
  have hG : Summable G := Summable.of_norm_bounded hsum (fun x => by simpa using hnorm (r x) 1)
  let q : Γ ⧸ K.comap c → Set Γ := fun x => dc K c (r x)
  have hfib : ∀ b : Set Γ, ∑' y : {x // q x = b}, F y.1 = B γ * ∑' y : {x // q x = b}, G y.1 := by
    intro b
    by_cases hb : ∃ x0, q x0 = b
    swap
    · push_neg at hb
      haveI : IsEmpty {x // q x = b} := ⟨fun y => hb y.1 y.2⟩
      simp [tsum_empty]
    obtain ⟨x0, rfl⟩ := hb
    obtain ⟨C, hC⟩ := hex (r x0) (hr_fix x0)
    have memfib : ∀ x, q x = q x0 ↔ r x ∈ dc K c (r x0) := fun x =>
      ⟨fun h => by rw [← show dc K c (r x) = dc K c (r x0) from h]; exact mem_dc_self K c _,
       fun h => dc_eq_of_mem K c h⟩
    have hval : ∀ δ ∈ C, ∃ k, k ∈ K ∧ c k = k ∧ r (QuotientGroup.mk δ) = δ * k := by
      intro δ hδ
      obtain ⟨h, hh, he⟩ := out_mk K c δ
      exact ⟨c h, hh, hc h, by show c (Quotient.out _) = _; rw [he, map_mul, (hC.1 δ hδ).1]⟩
    have haδ : ∀ δ ∈ C, ∀ k, k ∈ K → a (δ * k) = a (r x0) := by
      intro δ hδ k hk
      obtain ⟨_, k₁, k₂, h1, -, h3, -, hδe⟩ := hC.1 δ hδ
      rw [hδe, ← ha (r x0) k₁ (k₂ * k) h1 (K.mul_mem h3 hk)]
      simp [mul_assoc]
    have hFv : ∀ δ ∈ C, F (QuotientGroup.mk δ) = a (r x0) • B (γ * δ) := by
      intro δ hδ
      obtain ⟨k, hk, -, he⟩ := hval δ hδ
      show a (r _) • B (γ * r _) = _
      rw [he, haδ δ hδ k hk, ← mul_assoc, hB _ _ hk]
    have hGv : ∀ δ ∈ C, G (QuotientGroup.mk δ) = a (r x0) • B δ := by
      intro δ hδ
      obtain ⟨k, hk, -, he⟩ := hval δ hδ
      show a (r _) • B (r _) = _
      rw [he, haδ δ hδ k hk, hB _ _ hk]
    let e : C → {x // q x = q x0} := fun δ => ⟨QuotientGroup.mk δ.1, (memfib _).2 (by
      obtain ⟨k, hk, hck, he⟩ := hval δ.1 δ.2
      rw [he]
      obtain ⟨_, k₁, k₂, h1, h2, h3, h4, hδe⟩ := hC.1 δ.1 δ.2
      exact mul_mem_dc K c ⟨k₁, k₂, h1, h2, h3, h4, hδe⟩ hk hck)⟩
    have hinj : Function.Injective e := by
      rintro ⟨δ, hδ⟩ ⟨δ', hδ'⟩ h
      have h' : (QuotientGroup.mk δ : Γ ⧸ K.comap c) = QuotientGroup.mk δ' := congrArg Subtype.val h
      have hfix : c (δ⁻¹ * δ') = δ⁻¹ * δ' := by rw [map_mul, map_inv, (hC.1 δ hδ).1, (hC.1 δ' hδ').1]
      rw [QuotientGroup.eq, Subgroup.mem_comap, hfix] at h'
      apply Subtype.ext
      exact (hC.2 δ' (hC.1 δ' hδ').2).unique ⟨hδ, h', hfix⟩ ⟨hδ', by simp, by simp⟩
    have hsurj : Function.Surjective e := by
      rintro ⟨x, hx⟩
      obtain ⟨k₁, k₂, h1, h2, h3, h4, hxe⟩ := (memfib x).1 hx
      obtain ⟨δ, ⟨hδ, hK, -⟩, -⟩ := hC.2 (r x) ⟨k₁, k₂, h1, h2, h3, h4, hxe⟩
      refine ⟨⟨δ, hδ⟩, Subtype.ext ?_⟩
      show (QuotientGroup.mk δ : Γ ⧸ K.comap c) = x
      conv_rhs => rw [← QuotientGroup.out_eq' x]
      rw [QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv, (hC.1 δ hδ).1]
      exact hK
    have hT : ∀ f : Γ ⧸ K.comap c → (H →L[ℂ] H),
        ∑' y : {x // q x = q x0}, f y.1 = ∑ δ ∈ C, f (QuotientGroup.mk δ) := by
      intro f
      rw [← Equiv.tsum_eq (Equiv.ofBijective e ⟨hinj, hsurj⟩) (fun y : {x // q x = q x0} => f y.1), tsum_fintype]
      exact Finset.sum_coe_sort C (fun δ => f (QuotientGroup.mk δ))
    rw [hT, hT, Finset.sum_congr rfl hFv, Finset.sum_congr rfl hGv, ← Finset.smul_sum, ← Finset.smul_sum,
      hH (r x0) C (hr_fix x0) hC γ, mul_smul_comm]
  let eσ := Equiv.sigmaFiberEquiv q
  have hFs : HasSum (fun b : Set Γ => ∑' y : {x // q x = b}, F y.1) (∑' x, F x) :=
    HasSum.sigma ((eσ.hasSum_iff).2 hF.hasSum) (fun b => (hF.comp_injective Subtype.val_injective).hasSum)
  have hGs : HasSum (fun b : Set Γ => ∑' y : {x // q x = b}, G y.1) (∑' x, G x) :=
    HasSum.sigma ((eσ.hasSum_iff).2 hG.hasSum) (fun b => (hG.comp_injective Subtype.val_injective).hasSum)
  have hGm := hGs.mul_left (B γ)
  rw [← funext hfib] at hGm
  have := hFs.unique hGm
  show HasSum F _
  rw [← this]
  exact hF.hasSum
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.UpInj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levW_le_GfC (R : RealDat D A Ks) (i : Fin D.R.m) {k : GA D (Wc D i)} (hk : k ∈ levW R i) :
    k ∈ GfC (Wc D i) := hk.1

theorem mem_locK_iff (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC (Wc D i)) :
    (g : GA D (Wc D i)) ∈ {k | k ∈ levW R i ∧ SuppF (Wc D i) (GlobalTheory.LevelProduct.fE D v) k} ↔
      g ∈ KR R i ∧ cf (Wc D i) v g = g := by
  simp only [Set.mem_setOf_eq, KR, Subgroup.mem_subgroupOf, cf_eq_self_iff]

theorem dcRep_exists (R : RealDat D A Ks) (i : Fin D.R.m) (hT : TransLaws R i)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (α : GfC (Wc D i)) (hα : cf (Wc D i) v α = α) :
    ∃ C, DCRep (cf (Wc D i) v) (KR R i) α C := by
  classical
  obtain ⟨C, hsupp, hrep⟩ := hT.1 v _ (isFinIdem_fE v) α ((cf_eq_self_iff _ v α).1 hα)
  refine ⟨C.subtype (· ∈ GfC (Wc D i)), fun δ hδ => ?_, fun x ⟨k₁, k₂, h1, h2, h3, h4, hx⟩ => ?_⟩
  · rw [Finset.mem_subtype] at hδ
    refine ⟨(cf_eq_self_iff _ v δ).2 (hsupp _ hδ), ?_⟩
    obtain ⟨-, k₁, hk₁, k₂, hk₂, he⟩ := hrep.1 _ hδ
    refine ⟨⟨k₁, levW_le_GfC R i hk₁.1⟩, ⟨k₂, levW_le_GfC R i hk₂.1⟩, ?_⟩
    obtain ⟨a1, a2⟩ := (mem_locK_iff R i v ⟨k₁, levW_le_GfC R i hk₁.1⟩).1 hk₁
    obtain ⟨b1, b2⟩ := (mem_locK_iff R i v ⟨k₂, levW_le_GfC R i hk₂.1⟩).1 hk₂
    exact ⟨a1, a2, b1, b2, Subtype.ext he⟩
  · have hk₁ := (mem_locK_iff R i v k₁).2 ⟨h1, h2⟩
    have hk₂ := (mem_locK_iff R i v k₂).2 ⟨h3, h4⟩
    have hx' : (x : GA D (Wc D i)) = (k₁ : GA D (Wc D i)) * α * k₂ := by rw [hx]; rfl
    obtain ⟨γ, ⟨hγC, hγK⟩, huniq⟩ := hrep.2 x ⟨_, hk₁, _, hk₂, hx'⟩
    have hγG : γ ∈ GfC (Wc D i) := (hrep.1 γ hγC).1
    have e : ((⟨γ, hγG⟩⁻¹ * x : GfC (Wc D i)) : GA D (Wc D i)) = γ⁻¹ * (x : GA D (Wc D i)) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hm := (mem_locK_iff R i v (⟨γ, hγG⟩⁻¹ * x)).1 (by rw [e]; exact hγK)
    refine ⟨⟨γ, hγG⟩, ⟨Finset.mem_subtype.2 hγC, hm⟩, ?_⟩
    rintro δ ⟨hδC, hδK, hδc⟩
    have e' : ((δ⁻¹ * x : GfC (Wc D i)) : GA D (Wc D i)) = (δ : GA D (Wc D i))⁻¹ * (x : GA D (Wc D i)) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hm' := (mem_locK_iff R i v (δ⁻¹ * x)).2 ⟨hδK, hδc⟩
    rw [e'] at hm'
    exact Subtype.ext (huniq (δ : GA D (Wc D i)) ⟨Finset.mem_subtype.1 hδC, hm'⟩)

theorem isCosetRep_map (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) (α : GfC (Wc D i))
    (C : Finset (GfC (Wc D i))) (hC : DCRep (cf (Wc D i) v) (KR R i) α C) :
    (∀ γ ∈ C.map (Function.Embedding.subtype _), SuppF (Wc D i) (GlobalTheory.LevelProduct.fE D v) γ) ∧
      IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) (GlobalTheory.LevelProduct.fE D v) k} α
        (C.map (Function.Embedding.subtype _)) := by
  classical
  refine ⟨fun γ hγ => ?_, fun γ hγ => ?_, fun x ⟨k₁, hk₁, k₂, hk₂, hx⟩ => ?_⟩
  · obtain ⟨δ, hδ, rfl⟩ := Finset.mem_map.1 hγ
    exact (cf_eq_self_iff _ v δ).1 (hC.1 δ hδ).1
  · obtain ⟨δ, hδ, rfl⟩ := Finset.mem_map.1 hγ
    obtain ⟨-, k₁, k₂, h1, h2, h3, h4, he⟩ := hC.1 δ hδ
    refine ⟨δ.2, k₁, (mem_locK_iff R i v k₁).2 ⟨h1, h2⟩, k₂, (mem_locK_iff R i v k₂).2 ⟨h3, h4⟩, ?_⟩
    simp [he]
  · have g₁ := levW_le_GfC R i hk₁.1
    have g₂ := levW_le_GfC R i hk₂.1
    have hxG : x ∈ GfC (Wc D i) := by
      rw [hx]; exact (GfC (Wc D i)).mul_mem ((GfC (Wc D i)).mul_mem g₁ α.2) g₂
    obtain ⟨a1, a2⟩ := (mem_locK_iff R i v ⟨k₁, g₁⟩).1 hk₁
    obtain ⟨b1, b2⟩ := (mem_locK_iff R i v ⟨k₂, g₂⟩).1 hk₂
    have hx2 : (⟨x, hxG⟩ : GfC (Wc D i)) = ⟨k₁, g₁⟩ * α * ⟨k₂, g₂⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact hx
    have hex := hC.2 ⟨x, hxG⟩ ⟨_, _, a1, a2, b1, b2, hx2⟩
    obtain ⟨δ, ⟨hδC, hδK, hδc⟩, huniq⟩ := hex
    have hm := (mem_locK_iff R i v (δ⁻¹ * (⟨x, hxG⟩ : GfC (Wc D i)))).2 ⟨hδK, hδc⟩
    have e : ((δ⁻¹ * (⟨x, hxG⟩ : GfC (Wc D i)) : GfC (Wc D i)) : GA D (Wc D i)) = (δ : GA D (Wc D i))⁻¹ * x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e] at hm
    refine ⟨(δ : GA D (Wc D i)), ⟨Finset.mem_map_of_mem _ hδC, hm⟩, ?_⟩
    rintro γ ⟨hγC, hγK⟩
    obtain ⟨δ', hδ', rfl⟩ := Finset.mem_map.1 hγC
    have e' : ((δ'⁻¹ * (⟨x, hxG⟩ : GfC (Wc D i)) : GfC (Wc D i)) : GA D (Wc D i)) = (δ' : GA D (Wc D i))⁻¹ * x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    obtain ⟨c1, c2⟩ := (mem_locK_iff R i v (δ'⁻¹ * (⟨x, hxG⟩ : GfC (Wc D i)))).1 (by rw [e']; exact hγK)
    exact congrArg Subtype.val (huniq δ' ⟨hδ', c1, c2⟩)

theorem heckeReps : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m),
    TransLaws R i → ∀ (B : GfC (Wc D i) → ((R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H)),
    (∀ (γ : GfC (Wc D i)) x y, trPair R i (γ : GA D (Wc D i)) x y = ⟪x, B γ y⟫_ℂ) →
    (∀ v α, GlobalTheory.UpInj.cf (Wc D i) v α = α → ∃ C, GlobalTheory.UpInj.DCRep (GlobalTheory.UpInj.cf (Wc D i) v) (GlobalTheory.UpInj.KR R i) α C) ∧
    (∀ v α C, GlobalTheory.UpInj.cf (Wc D i) v α = α → GlobalTheory.UpInj.DCRep (GlobalTheory.UpInj.cf (Wc D i) v) (GlobalTheory.UpInj.KR R i) α C →
      ∀ γ, ∑ δ ∈ C, B (γ * δ) = B γ * ∑ δ ∈ C, B δ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hT B hB
  refine ⟨fun v α hα => dcRep_exists R i hT v α hα, fun v α C hα hC γ => ?_⟩
  obtain ⟨hs, hr⟩ := isCosetRep_map R i v α C hC
  have hB1 : ∀ y, B 1 y = y := fun y => ext_inner_left ℂ fun x => by
    rw [← hB, OneMemClass.coe_one, hT.2.2.2.2.2]
  have key : ∀ (γ : GfC (Wc D i)) y y', (∀ γ ∈ GfC (Wc D i), ∀ x, trPair R i γ x y' =
      ∑ δ ∈ C.map (Function.Embedding.subtype _), trPair R i (γ * δ) x y) →
      B γ y' = (∑ δ ∈ C, B (γ * δ)) y := fun γ y y' h => ext_inner_left ℂ fun x => by
    rw [← hB, h γ γ.2 x, Finset.sum_map, ContinuousLinearMap.sum_apply, inner_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [← hB]; rfl
  ext y
  obtain ⟨y', -, hy'⟩ := hT.2.1 v _ (isFinIdem_fE v) α ((cf_eq_self_iff _ v α).1 hα) _ hs hr y
  have e1 := key 1 y y' hy'
  simp only [one_mul, hB1] at e1
  rw [ContinuousLinearMap.mul_apply, ← e1, key γ y y' hy']

end GlobalTheory.UpInj

end
end
