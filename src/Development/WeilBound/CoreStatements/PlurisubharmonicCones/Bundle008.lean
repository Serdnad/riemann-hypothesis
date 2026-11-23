module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle061
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle068
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle095
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace LevelTowerAlt.LocFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

noncomputable def rg (R : RiemLat E g Λ) {N : ℕ} (e : Fin N → Λ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun k l => (R.ip (R.P (e k)) (R.P (e l))).re

theorem conj_ip (R : RiemLat E g Λ) (x y : Fin g → ℂ) : star (R.ip y x) = R.ip x y := by
  show star (x ⬝ᵥ R.Hm *ᵥ star y) = y ⬝ᵥ R.Hm *ᵥ star x
  rw [← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]

theorem rg_symm (R : RiemLat E g Λ) {N : ℕ} (e : Fin N → Λ) : (rg R e)ᵀ = rg R e := by
  ext k l
  simp only [rg, transpose_apply, of_apply]
  rw [← conj_ip R (R.P (e l)) (R.P (e k))]
  simp

theorem ip_sum (R : RiemLat E g Λ) {N : ℕ} (u : Fin N → Fin g → ℂ) (x y : Fin N → ℝ) :
    (R.ip (∑ k, (x k : ℂ) • u k) (∑ l, (y l : ℂ) • u l)).re = ∑ k, ∑ l, x k * (R.ip (u k) (u l)).re * y l := by
  have : R.ip (∑ k, (x k : ℂ) • u k) (∑ l, (y l : ℂ) • u l) =
      ∑ k, ∑ l, (x k : ℂ) * R.ip (u k) (u l) * (y l : ℂ) := by
    unfold RiemLat.ip
    rw [star_sum, mulVec_sum, dotProduct_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_dotProduct]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    rw [show star (x k : ℂ) = (x k : ℂ) from Complex.conj_ofReal _]
    ring
  rw [this, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp

theorem rg_pos (R : RiemLat E g Λ) {N : ℕ} (e : Module.Basis (Fin N) ℤ Λ) (x : Fin N → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ rg R e *ᵥ x := by
  have h1 : x ⬝ᵥ rg R e *ᵥ x =
      (R.ip (∑ k, (x k : ℂ) • R.P (e k)) (∑ l, (x l : ℂ) • R.P (e l))).re := by
    rw [ip_sum]
    simp only [dotProduct, mulVec, rg, of_apply, Finset.mul_sum, mul_assoc]
  rw [h1]
  refine R.pos _ fun h0 => hx ?_
  funext k
  obtain ⟨w, hw⟩ := R.unimod.2 (e.coord k)
  have h2 : ∀ l, R.form (e l) w = -(if l = k then 1 else 0) := by
    intro l
    have ha := R.alt (e l + w)
    simp only [map_add (f := _), LinearMap.add_apply, R.alt] at ha
    have hb : R.form w (e l) = if l = k then 1 else 0 := by
      rw [hw]; simp [Finsupp.single_apply]
    linarith
  have h3 : ((∑ l, (x l : ℂ) • R.P (e l)) ⬝ᵥ R.Hm *ᵥ star (R.P w)).im = ∑ l, x l * (R.form (e l) w : ℝ) := by
    rw [sum_dotProduct, Complex.im_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_dotProduct, smul_eq_mul, Complex.im_ofReal_mul, R.im]
  rw [h0] at h3
  simp only [h2] at h3
  simpa using h3

theorem rg_coords (R : RiemLat E g Λ) {N m : ℕ} (e : Module.Basis (Fin N) ℤ Λ) (v : Fin m → Λ) :
    rg R v = (coords e v).map (Int.castRingHom ℝ) * rg R e * ((coords e v).map (Int.castRingHom ℝ))ᵀ := by
  have h : ∀ i, R.P (v i) = ∑ k, (((e.repr (v i) k : ℤ) : ℝ) : ℂ) • R.P (e k) := by
    intro i
    conv_lhs => rw [← e.sum_repr (v i)]

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, Complex.ofReal_intCast, Int.cast_smul_eq_zsmul]
  ext i j
  have : rg R v i j = ∑ k, ∑ l, ((e.repr (v i) k : ℤ) : ℝ) * (R.ip (R.P (e k)) (R.P (e l))).re *
      ((e.repr (v j) l : ℤ) : ℝ) := by
    rw [← ip_sum, ← h, ← h]
    rfl
  rw [this, Finset.sum_comm]
  simp only [Matrix.mul_apply, Finset.sum_mul, map_apply, transpose_apply, coords, rg, of_apply, eq_intCast]

end LevelTowerAlt.LocFin

open LevelTowerAlt.LocFin in
theorem LevelTowerAlt.cusps_locally_finite_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ), IsOpen U → IsHolFam U R → IsCMFam σ → (∀ t ∈ U, (R t).HasRank σ m) → ∀ t₀ ∈ U, ∃ (ε : ℝ) (F : Finset (Submodule (𝓞 E) Λ)), 0 < ε ∧ ∀ t ∈ U ∩ Metric.ball t₀ ε, (∀ I ∈ F, (R t).IsCusp I) ∧ ∀ I, (R t).IsCusp I → (R t).nz σ I ≤ 1 → I ∈ F := by
  intro E _ _ _ g Λ _ _ Ψ _ n U R σ m hU hHol hCM _ t₀ ht₀
  classical
  haveI := (R t₀).free
  haveI := (R t₀).fin
  let e := Module.finBasis ℤ Λ
  have hHm : ∀ i j, ContinuousOn (fun t => (R t).Hm i j) U := by
    intro i j
    obtain ⟨h1, h2⟩ := (GlobalTheory.T.holomorphic_family_smooth_entries E g Λ Ψ n U R hU hHol).1 i j
    have e : (fun t => (R t).Hm i j) = fun t => (((R t).Hm i j).re : ℂ) + (((R t).Hm i j).im : ℂ) * Complex.I := by
      funext t; exact (Complex.re_add_im _).symm
    rw [e]
    exact (Complex.continuous_ofReal.comp_continuousOn h1.continuousOn).add
      ((Complex.continuous_ofReal.comp_continuousOn h2.continuousOn).mul continuousOn_const)
  have hip : ∀ x y, ContinuousOn (fun t => (R t).ip ((R t).P x) ((R t).P y)) U := by
    intro x y
    unfold RiemLat.ip
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    refine continuousOn_finsetSum _ fun i _ => ((continuousOn_pi.1 (hHol.2 y).continuousOn i)).mul ?_
    refine continuousOn_finsetSum _ fun j _ => (hHm i j).mul ?_
    exact (continuous_star.comp_continuousOn (continuousOn_pi.1 (hHol.2 x).continuousOn j))
  have hS : ContinuousOn (fun t => rg (R t) e) U :=
    continuousOn_pi.2 fun k => continuousOn_pi.2 fun l =>
      Complex.continuous_re.comp_continuousOn (hip (e k) (e l))
  obtain ⟨c, hc, hev⟩ := unif_pos (rg (R t₀) e) (rg_pos (R t₀) e)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((hS.continuousAt (hU.mem_nhds ht₀)).eventually hev)
  obtain ⟨Dk, hDk⟩ : ∃ Dk : ℝ, Dk = |(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ)) := ⟨_, rfl⟩
  have hD0 : 0 ≤ Dk := hDk ▸ Real.rpow_nonneg (abs_nonneg _) _
  have hfin := (finite_sat e ⌈(max 1 (Dk / c)) ^ Module.finrank ℤ Λ⌉).preimage
    (SetLike.coe_injective (A := Submodule (𝓞 E) Λ)).injOn
  have hcusp : ∀ t ∈ U, ∀ t' ∈ U, ∀ I, (R t).IsCusp I → (R t').IsCusp I := fun t ht t' ht' I h =>
    ⟨h.1, h.2.1, hHol.1 t ht t' ht' ▸ h.2.2⟩
  refine ⟨ε, hfin.toFinset.filter fun I => (R t₀).IsCusp I, hε, fun t ht =>
    ⟨fun I hI => hcusp t₀ ht₀ t ht.1 I (Finset.mem_filter.1 hI).2, fun I hI hnz => ?_⟩⟩
  refine Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ?_, hcusp t ht.1 t₀ ht₀ I hI⟩
  have hinj : Function.Injective (I.subtype.toAddMonoidHom.toIntLinearMap) := Subtype.val_injective
  haveI : Module.Finite ℤ I := Module.Finite.of_injective _ hinj
  haveI : Module.IsTorsionFree ℤ I := Function.Injective.moduleIsTorsionFree _ hinj (fun _ _ => map_smul _ _ _)
  haveI : Module.Free ℤ I := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ I
  have hli : LinearIndependent ℤ fun i => (b i : Λ) :=
    b.linearIndependent.map' (I.subtype.toAddMonoidHom.toIntLinearMap) (LinearMap.ker_eq_bot.2 hinj)
  obtain ⟨hm, hdet⟩ := GlobalTheory.T.isotropic_sublattice_gram_determinant E g Λ Ψ (R t) σ I hCM hI.2.2 hI.1 _ b
  obtain ⟨⟨r, v, hv⟩, hN⟩ := GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ (R t) σ I hCM hI.2.2 hI.1
  have hnz0 := (hN r v hv).2.1
  obtain ⟨hd0, hd1⟩ := det_bound (coords e fun i => (b i : Λ)) (det_ne_zero e hli) (rg (R t) e)
    (rg_symm _ _) hc (hball t ht.2)
  rw [← rg_coords] at hd1
  have hle : Module.finrank ℤ I ≤ Module.finrank ℤ Λ := by
    simpa using hli.fintype_card_le_finrank
  refine ⟨_, fun i => (b i : Λ), fun x => ⟨fun hx => ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩, ?_⟩,
    fun x k hk hx => hI.2.1 x k hk hx, hd0, ?_⟩
  · have := congrArg (I.subtype.toAddMonoidHom.toIntLinearMap) (b.sum_repr ⟨x, hx⟩)

    rw [map_sum] at this
    simpa using this
  · rintro ⟨y, rfl⟩
    exact I.sum_mem fun i _ => zsmul_mem (b i).2 _
  · have h1 : (rg (R t) fun i => (b i : Λ)).det ≤ Dk ^ Module.finrank ℤ I := by
      refine hdet.le.trans ?_
      rw [← hDk, hm, mul_assoc, mul_comm 2, pow_mul Dk _ 2]
      have h0 : 0 ≤ Dk ^ (Fintype.card Ψ * Module.finrank (𝓞 E) I) := pow_nonneg hD0 _
      exact pow_le_pow_left₀ (mul_nonneg hnz0.le h0) (mul_le_of_le_one_left h0 hnz) 2
    have h2 : (((coords e fun i => (b i : Λ)) * (coords e fun i => (b i : Λ))ᵀ).det : ℝ) ≤
        (Dk / c) ^ Module.finrank ℤ I := by
      rw [div_pow, le_div_iff₀ (pow_pos hc _), mul_comm]
      exact hd1.trans h1
    have h3 : (Dk / c) ^ Module.finrank ℤ I ≤ (max 1 (Dk / c)) ^ Module.finrank ℤ Λ :=
      (pow_le_pow_left₀ (div_nonneg hD0 hc.le) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) hle)
    exact_mod_cast (h2.trans h3).trans (Int.le_ceil _)
end

section

noncomputable section

namespace LevelTowerAlt.Comparison₂

open Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB

variable {e e' : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] {A : FinHolAtlas e X} {A' : FinHolAtlas e' Z}

theorem holo_mono {U V : Set X} {g : X → ℂ} (h : A.HoloOn U g) (hVU : V ⊆ U) : A.HoloOn V g :=
  fun j => (h j).mono fun _ hy => ⟨hy.1, hVU hy.2⟩

theorem holo_cont {U : Set X} {g : X → ℂ} (h : A.HoloOn U g) {x : X} (hx : x ∈ U) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  have hc := (h j _ ⟨(A.chart j).map_source hj, by rwa [Set.mem_preimage, (A.chart j).left_inv hj]⟩).continuousAt
  refine (hc.comp ((A.chart j).continuousAt hj)).congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem holo_comp {U : Set Z} {g : Z → ℂ} (hg : A'.HoloOn U g) {h : X → Z} (hh : HoloMap A A' h) :
    A.HoloOn (h ⁻¹' U) (g ∘ h) := by
  intro j y hy
  obtain ⟨k, hk⟩ := A'.cover (h ((A.chart j).symm y))
  have h1 := hh.2 j k y ⟨hy.1, hk⟩
  have h2 := hg k (A'.chart k (h ((A.chart j).symm y)))
    ⟨(A'.chart k).map_source hk, by rw [Set.mem_preimage, (A'.chart k).left_inv hk]; exact hy.2⟩
  refine (AnalyticAt.comp (f := A'.chart k ∘ h ∘ (A.chart j).symm) h2 h1).congr ?_
  have hc : ContinuousAt (h ∘ (A.chart j).symm) y := hh.1.continuousAt.comp ((A.chart j).continuousAt_symm hy.1)
  filter_upwards [hc.eventually_mem ((A'.chart k).open_source.mem_nhds hk)] with y' hy'
  have : (A'.chart k).symm (A'.chart k (h ((A.chart j).symm y'))) = h ((A.chart j).symm y') := (A'.chart k).left_inv hy'
  simp [this]

def LocRe (A : FinHolAtlas e X) (u : X → ℝ) (x : X) : Prop :=
  ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, u y = (G y).re

theorem LocRe.congr {u u' : X → ℝ} {x : X} (h : LocRe A u x) (hu : ∀ᶠ y in 𝓝 x, u' y = u y) : LocRe A u' x := by
  obtain ⟨V, hV, hx, G, hG, h⟩ := h
  obtain ⟨W, hW, hWo, hxW⟩ := eventually_nhds_iff.1 hu
  exact ⟨V ∩ W, hV.inter hWo, ⟨hx, hxW⟩, G, holo_mono hG Set.inter_subset_left, fun y hy => (hW y hy.2).trans (h y hy.1)⟩

theorem LocRe.zero (x : X) : LocRe A (fun _ => 0) x :=
  ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ _ _ => analyticAt_const, fun _ _ => rfl⟩

theorem LocRe.add {u u' : X → ℝ} {x : X} (h : LocRe A u x) (h' : LocRe A u' x) : LocRe A (fun y => u y + u' y) x := by
  obtain ⟨V, hV, hx, G, hG, h⟩ := h
  obtain ⟨V', hV', hx', G', hG', h'⟩ := h'
  exact ⟨V ∩ V', hV.inter hV', ⟨hx, hx'⟩, _, holoOn_add A hG hG', fun y hy => by simp [h y hy.1, h' y hy.2]⟩

theorem LocRe.mul {u : X → ℝ} {x : X} (h : LocRe A u x) (c : ℝ) : LocRe A (fun y => c * u y) x := by
  obtain ⟨V, hV, hx, G, hG, h⟩ := h
  exact ⟨V, hV, hx, _, holoOn_mul A hG c, fun y hy => by simp [h y hy]⟩

theorem LocRe.sum {I : Type} (s : Finset I) {u : I → X → ℝ} {x : X} (h : ∀ i ∈ s, LocRe A (u i) x) :
    LocRe A (fun y => ∑ i ∈ s, u i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LocRe.zero x
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (by simp)).add (ih fun j hj => h j (by simp [hj]))

theorem LocRe.comp {u : Z → ℝ} {h : X → Z} (hh : HoloMap A A' h) {x : X} (hu : LocRe A' u (h x)) : LocRe A (fun y => u (h y)) x := by
  obtain ⟨V, hV, hx, G, hG, hu⟩ := hu
  exact ⟨h ⁻¹' V, hV.preimage hh.1, hx, _, holo_comp hG hh, fun y hy => hu _ hy⟩

theorem LocRe.log {U : Set X} (hU : IsOpen U) {f : X → ℂ} (hf : A.HoloOn U f) {x : X} (hx : x ∈ U) (h0 : f x ≠ 0) :
    LocRe A (fun y => Real.log ‖f y‖) x := by
  have hc : ContinuousOn (fun y => f y / f x) U := fun y hy => ((holo_cont hf hy).div_const _).continuousWithinAt
  refine ⟨U ∩ (fun y => f y / f x) ⁻¹' Complex.slitPlane, hc.isOpen_inter_preimage hU Complex.isOpen_slitPlane,
    ⟨hx, by simp [div_self h0]⟩, fun y => Complex.log (f y / f x) + (Real.log ‖f x‖ : ℝ), fun j y hy => ?_, fun y hy => ?_⟩
  · exact (((hf j y ⟨hy.1, hy.2.1⟩).div_const (c := f x)).clog hy.2.2).add analyticAt_const
  · have h1 : f y ≠ 0 := fun h => by simpa [h] using hy.2
    simp [Complex.log_re, Real.log_div, h1, h0]

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem log_h_smul (L : HermLine J) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (L.h fun p => c p.1 * z p) = ∑ k, (L.a k : ℝ) * Real.log ‖c k‖ + Real.log (L.h z) := by
  have hp : ∀ k, ‖c k‖ ^ L.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [L.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => hp k) (L.pos z hz).ne', Real.log_prod fun k _ => hp k]
  simp only [Real.log_zpow]

theorem log_diff_orbit {L L' : HermLine J} (h : L.a = L'.a) {z z' : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0)
    (ho : SameOrbit z z') : Real.log (L.h z) - Real.log (L'.h z) = Real.log (L.h z') - Real.log (L'.h z') := by
  obtain ⟨c, hc, rfl⟩ := ho
  rw [log_h_smul L hc hz, log_h_smul L' hc hz, h]
  ring

theorem locRe_orbit (L : HermLine J) {U : Set X} (hU : IsOpen U) {s s' : X → (Σ k, J k) → ℂ}
    (hs : ∀ p, A.HoloOn U fun y => s y p) (hs' : ∀ p, A.HoloOn U fun y => s' y p) (hne : ∀ y ∈ U, ∀ k, ∃ i, s' y ⟨k, i⟩ ≠ 0)
    (ho : ∀ y ∈ U, SameOrbit (s y) (s' y)) {x : X} (hx : x ∈ U) :
    LocRe A (fun y => Real.log (L.h (s y)) - Real.log (L.h (s' y))) x := by
  choose i hi using hne x hx
  have hi' : ∀ k, s x ⟨k, i k⟩ ≠ 0 := fun k => by
    obtain ⟨c, hc, e⟩ := ho x hx
    rw [e]
    exact mul_ne_zero (hc k) (hi k)
  have h1 := LocRe.sum (A := A) Finset.univ (x := x) (u := fun k y => (L.a k : ℝ) *
      (Real.log ‖s y ⟨k, i k⟩‖ + -1 * Real.log ‖s' y ⟨k, i k⟩‖)) fun k _ =>
    ((LocRe.log hU (hs _) hx (hi' k)).add ((LocRe.log hU (hs' _) hx (hi k)).mul _)).mul _
  refine h1.congr ?_
  filter_upwards [hU.mem_nhds hx, eventually_all.2 fun k => (holo_cont (hs' ⟨k, i k⟩) hx).eventually_ne (hi k)] with y hy hy'
  obtain ⟨c, hc, e⟩ := ho y hy
  rw [e, log_h_smul L hc (hne y hy), add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc k)) (norm_ne_zero_iff.2 (hy' k))]
  ring

theorem psh_of_locRe {P Q : LocPot X} (hP : IsPotential A P) (hQ : IsPotential A Q)
    (h : ∀ x, LocRe A (fun y => P.φ x y - Q.φ x y) x) (hq : IsPsh A Q) : IsPsh A P := by
  have hz : A.Smooth (fun _ : X => (0 : ℝ)) := fun j => contDiffOn_const
  have h1 := (PshPull.isPsh_pull e e X X A A id (holoMap_id A) P Q (fun _ => 0) hP hQ hz (fun x _ => h x)).1
    (TailBoundAlt.isPsh_congr A _ _ hq (fun x y hy => hy.1) (by funext x y; exact add_zero _))
  exact TailBoundAlt.isPsh_congr A _ _ h1 (fun x y hy => ⟨hy, trivial⟩) (by funext x y; exact (add_zero _).symm)

theorem pot_rsmul {P : LocPot X} (hP : IsPotential A P) (c : ℝ) : IsPotential A (P.rsmul c) :=
  isPotential_mul A P hP c _ rfl fun _ _ => rfl

theorem exists_psh_pull [CompactSpace X] [T2Space X] {h : X → Z} (hh : HoloMap A A' h) {Θ : LocPot X} (hΘ : IsPotential A Θ)
    (hΘp : IsPosPot A Θ) {Θ' : LocPot Z} (hΘ' : IsPotential A' Θ') :
    ∃ C : ℝ, ∀ (P : LocPot X) (Q : LocPot Z), IsPotential A P → IsPotential A' Q → IsPsh A' (Q + Θ') →
      (∀ x, LocRe A (fun y => P.φ x y - Q.φ (h x) (h y)) x) → IsPsh A (P + Θ.rsmul C) := by
  have hp := isPotentialPullback A' A h hh Θ' hΘ'
  obtain ⟨C, -, -, hC⟩ := TailBoundAlt.exists_psh_chern_bound A Θ _ hΘ hΘp hp
  refine ⟨C, fun P Q hP hQ hq hl => ?_⟩
  have hz : A'.Smooth (fun _ : Z => (0 : ℝ)) := fun j => contDiffOn_const
  have hQ' := isPotentialAdd A' _ _ hQ hΘ'
  have hP' := isPotentialPullback A' A h hh _ hQ'
  have h1 := (PshPull.isPsh_pull e e' X Z A A' h hh _ (Q + Θ') (fun _ => 0) hP' hQ' hz
    (fun x _ => (LocRe.zero x).congr (Eventually.of_forall fun y => sub_self _))).1
    (TailBoundAlt.isPsh_congr A' _ _ hq (fun x y hy => hy.1) (by funext x y; exact add_zero _))
  have h2 : IsPsh A ((Q + Θ').pullback h hh.1) :=
    TailBoundAlt.isPsh_congr A _ _ h1 (fun x y hy => ⟨hy, trivial⟩) (by funext x y; exact (add_zero _).symm)
  have hR := isPotentialAdd A _ _ (pot_rsmul hΘ C) (pot_rsmul hp (-1))
  refine psh_of_locRe (isPotentialAdd A _ _ hP (pot_rsmul hΘ C)) (isPotentialAdd A _ _ hP' hR) (fun x => ?_)
    (isPshAdd A _ _ hP' hR h2 hC)
  refine (hl x).congr (Eventually.of_forall fun y => ?_)
  show P.φ x y + C * Θ.φ x y - (Q.φ (h x) (h y) + Θ'.φ (h x) (h y) + (C * Θ.φ x y + -1 * Θ'.φ (h x) (h y))) = _
  ring

end LevelTowerAlt.Comparison₂
end
end
