module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.NormSubOneLeOfHsdA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SquareIntegrableInnerProduct
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
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
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
public import Mathlib.Topology.Algebra.Constructions.DomMulAct

@[expose] public section

section

noncomputable section

open Finset Matrix MeasureTheory Topology
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def kUJA (ε : Fin n → Bool) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : Formalism.REAL.UJ ε :=
  ⟨⟨k, star k, Matrix.mem_unitaryGroup_iff.1 hk.1, Matrix.mem_unitaryGroup_iff'.1 hk.1⟩, by
    show Formalism.REAL.inUJ ε k
    rw [mir_inUJ_iff]
    show kᴴ * Jm ε * k = Jm ε
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
      Matrix.mem_unitaryGroup_iff'.1 hk.1, Matrix.one_mul]⟩

theorem cvA_equivariantA (hσ : IsURepOn (UJset ε) σ) {α : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hα : Continuous α) (hαc : HasCompactSupport α) (hαK : ∀ k ∈ Kset ε, ∀ g, α (k * g * star k) = α g)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (v : H) :
    σ k (cvA ε σ α v) = cvA ε σ α (σ k v) := by
  set κ := kUJA ε hk with hκdef
  have hκ : Formalism.MainNotions.S.umat κ = k := rfl
  have : (Formalism.REAL.muG ε).IsMulRightInvariant :=
    ⟨fun y => (measurePreserving_mul_right ε y).map_eq⟩
  have hmul : ∀ a b : Formalism.REAL.UJ ε,
      σ (Formalism.MainNotions.S.umat (a * b)) = (σ (Formalism.MainNotions.S.umat a)).comp (σ (Formalism.MainNotions.S.umat b)) :=
    fun a b => hσ.1.2 _ (umat_mem_UJset ε a) _ (umat_mem_UJset ε b)
  set F : Formalism.REAL.UJ ε → H := fun g => α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat (g * κ)) v with hF
  have hR : cvA ε σ α (σ k v) = ∫ g, F g ∂(Formalism.REAL.muG ε) := by
    unfold cvA
    congr 1
    funext g
    rw [hF]
    dsimp only
    rw [hmul, ContinuousLinearMap.comp_apply, hκ]
  have hL : σ k (cvA ε σ α v) = ∫ g, F (κ * g * κ⁻¹) ∂(Formalism.REAL.muG ε) := by
    unfold cvA
    rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_cvA hσ hα hαc v)]
    congr 1
    funext g
    have hc : Formalism.MainNotions.S.umat (κ * g * κ⁻¹) = k * Formalism.MainNotions.S.umat g * star k := rfl
    rw [hF]
    dsimp only
    rw [inv_mul_cancel_right, hc, hαK k hk, hmul, ContinuousLinearMap.comp_apply, hκ, map_smul]
  rw [hL, hR]
  calc ∫ g, F (κ * g * κ⁻¹) ∂(Formalism.REAL.muG ε) = ∫ g, F (g * κ⁻¹) ∂(Formalism.REAL.muG ε) :=
        integral_mul_left_eq_self (fun x => F (x * κ⁻¹)) κ
    _ = ∫ g, F g ∂(Formalism.REAL.muG ε) := integral_mul_right_eq_self F κ⁻¹

theorem map_le_isoA (T : H →ₗ[ℂ] H) (hT : ∀ k ∈ Formalism.REAL.Kset ε, ∀ v, σ k (T v) = T (σ k v))
    {μ : Fin n → ℝ} {S : Submodule ℂ H} (hS : Formalism.MainNotions.S.IsKTypeOf ε σ μ S) :
    S.map T ≤ sSup {S' | Formalism.MainNotions.S.IsKTypeOf ε σ μ S'} := by
  obtain ⟨hfin, hstab, hirr, ⟨w, hwS, hw0, hwt⟩, hdom⟩ := hS
  have hstab0 : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ LinearMap.ker T) := by
    intro g hg v hv
    rw [Submodule.mem_inf, LinearMap.mem_ker] at hv ⊢
    exact ⟨hstab g hg v hv.1, by rw [← hT g hg v, hv.2, _root_.map_zero]⟩
  rcases hirr _ inf_le_left hstab0 with h0 | h0
  · have hinj : ∀ x ∈ S, T x = 0 → x = 0 := fun x hx hTx => by
      have hx' : x ∈ S ⊓ LinearMap.ker T := Submodule.mem_inf.2 ⟨hx, LinearMap.mem_ker.2 hTx⟩
      rw [h0] at hx'
      exact (Submodule.mem_bot ℂ).1 hx'
    apply le_sSup
    show Formalism.MainNotions.S.IsKTypeOf ε σ μ (S.map T)
    unfold Formalism.MainNotions.S.IsKTypeOf
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · haveI : FiniteDimensional ℂ S := hfin
      infer_instance
    · rintro g hg _ ⟨x, hx, rfl⟩
      rw [hT g hg x]
      exact Submodule.mem_map_of_mem (hstab g hg x hx)
    · intro S' hS' hS'st
      have hst : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ S'.comap T) := by
        intro g hg v hv
        rw [Submodule.mem_inf, Submodule.mem_comap] at hv ⊢
        exact ⟨hstab g hg v hv.1, by rw [← hT g hg v]; exact hS'st g hg _ hv.2⟩
      rcases hirr _ inf_le_left hst with h1 | h1
      · left
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨x, hx, rfl⟩ := hS' hy
        have hx' : x ∈ S ⊓ S'.comap T := Submodule.mem_inf.2 ⟨hx, Submodule.mem_comap.2 hy⟩
        rw [h1, Submodule.mem_bot] at hx'
        rw [hx', _root_.map_zero]
        exact Submodule.zero_mem _
      · right
        refine le_antisymm hS' ?_
        rintro _ ⟨x, hx, rfl⟩
        have hx' : x ∈ S ⊓ S'.comap T := by rw [h1]; exact hx
        exact Submodule.mem_comap.1 (Submodule.mem_inf.1 hx').2
    · have hTw : T w ≠ 0 := fun h => hw0 (hinj w hwS h)
      refine ⟨T w, Submodule.mem_map_of_mem hwS, hTw, ?_⟩
      intro θ hθ
      rw [hT _ hθ w, hwt θ hθ, _root_.map_smul]
    · rintro μ' _ ⟨x, hx, rfl⟩ hne hwt'
      have hx0 : x ≠ 0 := fun h => hne (by rw [h, _root_.map_zero])
      refine hdom μ' x hx hx0 ?_
      intro θ hθ
      have h1 := hwt' θ hθ
      rw [hT _ hθ x] at h1
      refine sub_eq_zero.1 (hinj _ (Submodule.sub_mem _ (hstab _ hθ x hx) (Submodule.smul_mem _ _ hx)) ?_)
      rw [_root_.map_sub, h1, _root_.map_smul, sub_self]
  · rintro y ⟨x, hx, rfl⟩
    have hx' : x ∈ S ⊓ LinearMap.ker T := by rw [h0]; exact hx
    rw [LinearMap.mem_ker.1 (Submodule.mem_inf.1 hx').2]
    exact Submodule.zero_mem _

theorem exists_cvA_idA (hσ : IsURepOn (UJset ε) σ)
    (hadm : ∀ μ : Fin n → ℝ, FiniteDimensional ℂ
      (sSup {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H))
    (W : Submodule ℂ H) (hWf : FiniteDimensional ℂ W)
    (hWsum : W ≤ sSup {S : Submodule ℂ H | ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S})
    {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U) (h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ U) :
    ∃ α, AdmA ε U α ∧ ∀ w ∈ W, cvA ε σ α w = w := by
  classical
  let T : ∀ α, AdmA ε U α → H →ₗ[ℂ] H := fun α hα =>
    { toFun := cvA ε σ α
      map_add' := cvA_add_vec hσ hα.1.continuous hα.2.1
      map_smul' := fun c v => cvA_smul_vec α c v }
  have hTK : ∀ α (hα : AdmA ε U α), ∀ k ∈ Formalism.REAL.Kset ε, ∀ v, σ k (T α hα v) = T α hα (σ k v) :=
    fun α hα k hk v => cvA_equivariantA hσ hα.1.continuous hα.2.1 hα.2.2.2
      (by rw [← mir_Kset_eq]; exact hk) v
  have hWc : IsCompactElement W :=
    (Submodule.fg_iff_compact W).1 (Module.Finite.iff_fg.1 hWf)
  obtain ⟨t, hts, hWt⟩ :=
    (isCompactElement_iff_exists_le_sSup_of_le_sSup W).1 hWc _ hWsum
  let iso : Submodule ℂ H → Submodule ℂ H := fun S =>
    if h : ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S then sSup {S' | Formalism.MainNotions.S.IsKTypeOf ε σ h.choose S'} else ⊥
  haveI hisoF : ∀ S, FiniteDimensional ℂ (iso S) := by
    intro S
    by_cases h : ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S
    · have e : iso S = sSup {S' | Formalism.MainNotions.S.IsKTypeOf ε σ h.choose S'} := dif_pos h
      rw [e]
      exact hadm _
    · have e : iso S = ⊥ := dif_neg h
      rw [e]
      infer_instance
  let W2 := t.sup iso
  have hS_le : ∀ S ∈ t, S ≤ iso S ∧ ∀ α (hα : AdmA ε U α), S.map (T α hα) ≤ iso S := by
    intro S hS
    have h : ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S := hts hS
    simp only [iso, dif_pos h]
    exact ⟨le_sSup h.choose_spec, fun α hα => map_le_isoA (T α hα) (hTK α hα) h.choose_spec⟩
  have hWW2 : W ≤ W2 :=
    hWt.trans (Finset.sup_le fun S hS => (hS_le S hS).1.trans (Finset.le_sup (f := iso) hS))
  have hmapW : ∀ α (hα : AdmA ε U α), ∀ w ∈ W, cvA ε σ α w ∈ W2 := by
    intro α hα w hw
    have : W ≤ W2.comap (T α hα) :=
      hWt.trans (Finset.sup_le fun S hS => Submodule.map_le_iff_le_comap.1
        (((hS_le S hS).2 α hα).trans (Finset.le_sup (f := iso) hS)))
    exact this hw
  let b := Module.finBasis ℂ W
  let bw : Fin (Module.finrank ℂ W) → H := fun i => (b i : H)
  let R : Submodule ℂ (Fin (Module.finrank ℂ W) → W2) :=
    { carrier := {p | ∃ α, AdmA ε U α ∧ ∀ i, cvA ε σ α (bw i) = (p i : H)}
      add_mem' := by
        rintro p q ⟨α, hα, hp⟩ ⟨β, hβ, hq⟩
        exact ⟨α + β, hα.add hβ, fun i => by
          rw [cvA_add_fun hσ hα.1.continuous hα.2.1 hβ.1.continuous hβ.2.1, hp, hq]
          rfl⟩
      zero_mem' := ⟨0, AdmA.zero U, fun i => by rw [cvA_zero_fun]; rfl⟩
      smul_mem' := by
        rintro c p ⟨α, hα, hp⟩
        exact ⟨c • α, hα.smul c, fun i => by rw [cvA_smul_fun, hp]; rfl⟩ }
  have hRc : IsClosed (R : Set (Fin (Module.finrank ℂ W) → W2)) := R.closed_of_finiteDimensional
  let p0 : Fin (Module.finrank ℂ W) → W2 := fun i => ⟨bw i, hWW2 (b i).2⟩
  have hp0 : p0 ∈ closure (R : Set (Fin (Module.finrank ℂ W) → W2)) := by
    rw [Metric.mem_closure_iff]
    intro η hη
    obtain ⟨α, hα, hnear⟩ := exists_nearA hσ hU h1 bw (half_pos hη)
    refine ⟨fun i => ⟨cvA ε σ α (bw i), hmapW α hα _ (b i).2⟩, ⟨α, hα, fun i => rfl⟩, ?_⟩
    rw [dist_pi_lt_iff hη]
    intro i
    show dist (bw i) (cvA ε σ α (bw i)) < η
    rw [dist_comm, dist_eq_norm]
    linarith [hnear i]
  rw [hRc.closure_eq] at hp0
  obtain ⟨α, hα, hfix⟩ := hp0
  refine ⟨α, hα, ?_⟩
  have hext : (T α hα).comp W.subtype = W.subtype := b.ext fun i => hfix i
  intro w hw
  exact LinearMap.congr_fun hext ⟨w, hw⟩

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem rregRep_umat_inj (ε : Fin n → Bool) {x y : Formalism.REAL.UJ ε}
    (h : Formalism.MainNotions.S.umat x = Formalism.MainNotions.S.umat y) : x = y := Subtype.ext (Units.ext h)

theorem rregRep_rreg_umat (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) :
    rreg ε (Formalism.MainNotions.S.umat y) = rregG ε y := by
  have h : ∃ y' : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y' = Formalism.MainNotions.S.umat y := ⟨y, rfl⟩
  rw [rreg, dite_eq_left h]
  exact congrArg (rregG ε) (rregRep_umat_inj ε h.choose_spec)

theorem rregRep_rregG_apply (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) (f : L2 ε) :
    rregG ε y f = Lp.compMeasurePreserving (fun x : Formalism.REAL.UJ ε => x * y)
      (measurePreserving_mul_right ε y) f := by
  rw [rregG, dite_eq_left (measurePreserving_mul_right ε y)]
  rfl

private theorem Jm_mul_selfDiscreteSeriesExistence (ε : Fin n → Bool) :
    Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases h : ε i <;> simp [h]
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

private theorem Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  rw [Matrix.mul_assoc] at hg'
  simp only [Matrix.mul_assoc]
  rw [hg', Jm_mul_selfDiscreteSeriesExistence]

private theorem mul_Jm_conjTranspose_Jm_eq_one_of_mem_UJset (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : g * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = 1 := by
  have hl := Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset ε hg
  first
  | exact mul_eq_one_comm.mp hl
  | (rw [← Matrix.inv_eq_left_inv hl]
     exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse hl))

theorem rregRep_range (ε : Fin n → Bool) :
    Set.range (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) = UJset ε := by
  ext g
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hg
    exact ⟨⟨⟨g, Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, mul_Jm_conjTranspose_Jm_eq_one_of_mem_UJset ε hg,
      Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset ε hg⟩, hg⟩, rfl⟩

theorem rregRep_mem (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ y : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y = g := by
  have h2 : g ∈ Set.range (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y) := by
    rw [rregRep_range ε]
    exact hg
  obtain ⟨y, hy⟩ := h2
  exact ⟨y, hy⟩

theorem rregRep_one (ε : Fin n → Bool) : rreg ε 1 = 1 := by
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) := rfl
  rw [h1, rregRep_rreg_umat]
  ext1 f
  rw [rregRep_rregG_apply, ContinuousLinearMap.one_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_right ε 1)] with x hx
  rw [hx]
  simp

theorem rregRep_mul (ε : Fin n → Bool) (a b : Formalism.REAL.UJ ε) :
    rregG ε (a * b) = (rregG ε a).comp (rregG ε b) := by
  ext1 f
  rw [ContinuousLinearMap.comp_apply, rregRep_rregG_apply, rregRep_rregG_apply,
    rregRep_rregG_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_right ε (a * b)),
    Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (fun x : Formalism.REAL.UJ ε => x * b)
        (measurePreserving_mul_right ε b) f) (measurePreserving_mul_right ε a),
    (measurePreserving_mul_right ε a).quasiMeasurePreserving.ae_eq
      (Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_right ε b))] with x h1 h2 h3
  simp only [Function.comp_apply] at h1 h2 h3 ⊢
  rw [h1, h2, h3, mul_assoc]

theorem rregRep_cont (ε : Fin n → Bool) (v : L2 ε) :
    Continuous (fun y : Formalism.REAL.UJ ε => rregG ε y v) := by
  haveI : SMulInvariantMeasure (Formalism.REAL.UJ ε)ᵐᵒᵖ (Formalism.REAL.UJ ε) (Formalism.REAL.muG ε) := by
    refine ⟨fun c s hs => ?_⟩
    first
    | exact (measurePreserving_mul_right ε c.unop).measure_preimage hs.nullMeasurableSet
    | exact (measurePreserving_mul_right ε c.unop).measure_preimage hs
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by first | simp | exact ENNReal.ofNat_ne_top⟩
  have he : (fun y : Formalism.REAL.UJ ε => rregG ε y v) =
      fun y => (DomMulAct.mk (MulOpposite.op y)) • v := by
    funext y
    rw [rregRep_rregG_apply]
    rfl
  rw [he]
  have hm : Continuous (fun y : Formalism.REAL.UJ ε => DomMulAct.mk (MulOpposite.op y)) := by
    first
    | exact DomMulAct.continuous_mk.comp MulOpposite.continuous_op
    | exact DomMulAct.mkHomeomorph.continuous.comp MulOpposite.continuous_op
    | fun_prop
  haveI : OpensMeasurableSpace (Formalism.REAL.UJ ε)ᵐᵒᵖ :=
    ⟨MeasurableSpace.generateFrom_le fun s hs =>
      (IsOpen.preimage MulOpposite.continuous_op hs).measurableSet⟩
  exact hm.smul continuous_const

theorem rreg_isURepOn (ε : Fin n → Bool) : IsURepOn (UJset ε) (rreg ε) := by
  unfold IsURepOn
  refine ⟨⟨rregRep_one ε, ?_⟩, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨ya, rfl⟩ := rregRep_mem ε ha
    obtain ⟨yb, rfl⟩ := rregRep_mem ε hb
    have hab : Formalism.MainNotions.S.umat ya * Formalism.MainNotions.S.umat yb = Formalism.MainNotions.S.umat (ya * yb) := rfl
    rw [hab, rregRep_rreg_umat, rregRep_rreg_umat, rregRep_rreg_umat, rregRep_mul]
  · intro g hg v
    obtain ⟨y, rfl⟩ := rregRep_mem ε hg
    rw [rregRep_rreg_umat, rregRep_rregG_apply]
    exact Lp.norm_compMeasurePreserving v _
  · intro v
    obtain ⟨φ, hφc, hφ⟩ : ∃ φ : UJset ε → Formalism.REAL.UJ ε, Continuous φ ∧
        ∀ g : UJset ε, Formalism.MainNotions.S.umat (φ g) = g :=
      ⟨fun g => ⟨⟨(g : Matrix (Fin n) (Fin n) ℂ),
          Formalism.REAL.Jm ε * (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε,
          mul_Jm_conjTranspose_Jm_eq_one_of_mem_UJset ε g.2, Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset ε g.2⟩, g.2⟩,
        by
          apply Continuous.subtype_mk
          rw [Units.continuous_iff]
          constructor
          · exact continuous_subtype_val
          · exact (continuous_const.mul continuous_subtype_val.matrix_conjTranspose).mul
              continuous_const,
        fun g => rfl⟩
    have he : ∀ g : UJset ε, rreg ε (g : Matrix (Fin n) (Fin n) ℂ) v = rregG ε (φ g) v := by
      intro g
      rw [← hφ g, rregRep_rreg_umat]
    rw [continuousOn_iff_continuous_restrict]
    convert (rregRep_cont ε v).comp hφc using 1
    funext g
    exact he g

end ReciprocityTheory.ChartRestriction.DS
end
end
