module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle216
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormConsMul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle215
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle111
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle212
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle211
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle134
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle065
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle213
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Bool
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.deriv_integral_compact_support : ∀ {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (ρ : ℝ → Mat n → ℝ), Sm ρ → ∀ (K : Set (G n)), IsCompact K → ∀ (s₀ ε : ℝ), 0 < ε → (∀ s ∈ Metric.ball s₀ ε, ∀ y : G n, y ∉ K → ρ s y.val = 0) → HasDerivAt (fun s => ∫ y : G n, ρ s y.val ∂μ) (∫ y : G n, dt ρ s₀ y.val ∂μ) s₀ := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.IntDeriv.hasDerivAt_integral_compact | exact GlobalTheory.CompanionTheory.WaveSpd.IntDeriv.hasDerivAt_integral_compact | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.IntDeriv.hasDerivAt_integral_compact <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.energy_density_time_derivative : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] (u : ℝ → Mat n → W), Sm u → ∀ (s : ℝ), ∀ y ∈ GLs n, HasDerivAt (fun r => dens u r y) (2 * ⟪dt (dt u) s y, dt u s y⟫_ℝ + (1 / 2) * ∑ p : Ix n, ⟪Rr (hm p) (dt u s) y, Rt (hm p) u s y⟫_ℝ + 2 * ⟪dt u s y, u s y⟫_ℝ) s := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.hasDerivAt_dens | exact GlobalTheory.CompanionTheory.WaveSpd.hasDerivAt_dens | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.hasDerivAt_dens <;> assumption)
end

section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ConeHaar

theorem continuous_hOf (n : ℕ) : Continuous (hOf : (Fin n × Fin n → ℝ) → Mat n) := by
  unfold hOf
  fun_prop

theorem isClosed_posSemidef (n : ℕ) : IsClosed {M : Mat n | M.PosSemidef} := by
  have h : {M : Mat n | M.PosSemidef} =
      {M : Mat n | Mᴴ = M} ∩ ⋂ x : Fin n → ℂ, {M : Mat n | 0 ≤ star x ⬝ᵥ M *ᵥ x} := by
    ext M
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [h]
  refine IsClosed.inter (isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id) ?_
  refine isClosed_iInter fun x => isClosed_le continuous_const ?_
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

theorem measurableSet_cone (n : ℕ) : MeasurableSet (cone n) := by
  have h : cone n = (hOf ⁻¹' {M : Mat n | M.PosSemidef}) ∩
      ((fun v => (hOf v : Mat n).det) ⁻¹' {(0 : ℂ)}ᶜ) := by
    ext v
    simp only [cone, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun hv => ⟨hv.posSemidef, hv.det_pos.ne'⟩,
      fun hv => (Matrix.PosSemidef.posDef_iff_det_ne_zero hv.1).2 hv.2⟩
  rw [h]
  refine MeasurableSet.inter ((isClosed_posSemidef n).preimage (continuous_hOf n)).measurableSet ?_
  exact (isClosed_singleton.isOpen_compl.preimage
    (continuous_hOf n).matrix_det).measurableSet

theorem measurable_coneW (n : ℕ) : Measurable (coneW n) := by
  have h : Continuous fun v : Fin n × Fin n → ℝ => (hOf v : Mat n).det.re :=
    Complex.continuous_re.comp (continuous_hOf n).matrix_det
  unfold coneW
  exact ((h.measurable.pow_const n).inv).ennreal_ofReal

theorem coneW_toReal_smul (n : ℕ) (f : (Fin n × Fin n → ℝ) → ℂ) {v : Fin n × Fin n → ℝ}
    (hv : v ∈ cone n) : (coneW n v).toReal • f v = f v * ((hOf v).det ^ n)⁻¹ := by
  have hpos : (0 : ℂ) < (hOf v : Mat n).det := Matrix.PosDef.det_pos hv
  obtain ⟨hre, him⟩ := Complex.pos_iff.1 hpos
  have hdet : (hOf v : Mat n).det = (((hOf v : Mat n).det.re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simpa using him.symm)
  have hnn : 0 ≤ ((hOf v : Mat n).det.re ^ n)⁻¹ := inv_nonneg.2 (pow_nonneg hre.le n)
  unfold coneW
  rw [ENNReal.toReal_ofReal hnn, Complex.real_smul, mul_comm]
  congr 1
  conv_rhs => rw [hdet]
  push_cast
  rfl

theorem cone_integral : ∀ n : ℕ, (∀ᵐ v ∂(coneMeas n), v ∈ PositivityTheory.RgBcC.cone n) ∧ ∀ f : (Fin n × Fin n → ℝ) → ℂ, ∫ v, f v ∂(coneMeas n) = ∫ v in PositivityTheory.RgBcC.cone n, f v * ((hOf v).det ^ n)⁻¹ := by
  intro n
  refine ⟨?_, fun f => ?_⟩
  · exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem (measurableSet_cone n))
  · unfold coneMeas
    rw [integral_withDensity_eq_integral_toReal_smul₀ (measurable_coneW n).aemeasurable
      (Eventually.of_forall fun v => ENNReal.ofReal_lt_top) f]
    exact setIntegral_congr_fun (measurableSet_cone n) fun v hv => coneW_toReal_smul n f hv

end GlobalTheory.CompanionTheory.ConeHaar
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

section Per
variable {K : Type} [Field K] {W Y : Scheme.{0}} {q : Y ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Y}

theorem rs_topIso {V V' : Y.Opens} (h : V' ≤ V) (x : Γ(V, ⊤)) :
    rs h (V.topIso.hom.hom x) = V'.topIso.hom.hom ((Y.homOfLE h).appTop.hom x) := by
  rw [Scheme.homOfLE_appTop]
  simp only [rs, Scheme.Opens.topIso_hom, CommRingCat.comp_apply]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  rfl

def kerI (q : Y ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Y) (V : Y.Opens) : Ideal (Sec q V) := RingHom.ker (i.app V).hom

theorem one_P [CharZero K] [IsClosedImmersion i] (hAR : AffRel) (hQ : Cosieve (On q i)) {V : Y.Opens} {P : ObjectProperty (Thick (smFun Y q))}
    (hP : P = inU q V) {d d' : ℕ} (hc : Nonempty (Coord q V d)) (hc' : Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ V) d')) (b j : ℕ)
    (hj : j ≠ b) : Subsingleton ((RC (G q b) P hQ).H j) := by
  subst hP
  exact (hAR K W Y q i hQ V d d' hc hc' b).1 j hj

theorem inj_P [CharZero K] [IsClosedImmersion i] (hAR : AffRel) (hQ : Cosieve (On q i)) {V : Y.Opens} {P : ObjectProperty (Thick (smFun Y q))}
    (hP : P = inU q V) {d d' : ℕ} (hc : Nonempty (Coord q V d)) (hc' : Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ V) d')) (b : ℕ)
    (E : Om K (Sec q V) b →ₗ[K] HV q V b b) (hE : IsOm q V b E) :
    Function.Injective ((incl (G q b) P hQ).mapH b) := by
  subst hP
  exact ((hAR K W Y q i hQ V d d' hc hc' b).2 E hE (incl (G q b) (inU q V) hQ) fun _ _ => rfl).1

theorem range_P [CharZero K] [IsClosedImmersion i] (hAR : AffRel) (hQ : Cosieve (On q i)) {V : Y.Opens} {P : ObjectProperty (Thick (smFun Y q))}
    (hP : P = inU q V) {d d' : ℕ} (hc : Nonempty (Coord q V d)) (hc' : Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ V) d')) (b : ℕ)
    (E : Om K (Sec q V) b →ₗ[K] HV q V b b) (hE : IsOm q V b E) (ω : Om K (Sec q V) b) :
    castH (G q b) hP b (E ω) ∈ LinearMap.range ((incl (G q b) P hQ).mapH b) ↔
      ω ∈ relOm K (kerI q i V) b := by
  subst hP
  exact ((hAR K W Y q i hQ V d d' hc hc' b).2 E hE (incl (G q b) (inU q V) hQ) fun _ _ => rfl).2 ω

theorem pull_P {V V' : Y.Opens} {P P' : ObjectProperty (Thick (smFun Y q))} (hP : P = inU q V) (hP' : P' = inU q V') (k : P' ≤ P)
    (b : ℕ) (E : Om K (Sec q V) b →ₗ[K] HV q V b b) (E' : Om K (Sec q V') b →ₗ[K] HV q V' b b)
    (φ : Om K (Sec q V) b →ₗ[K] Om K (Sec q V') b)
    (h : ∀ (k' : inU q V' ≤ inU q V) ω, (resU (G q b) k').pull b (E ω) = E' (φ ω)) (ω : Om K (Sec q V) b) :
    (resU (G q b) k).pull b (castH (G q b) hP b (E ω)) = castH (G q b) hP' b (E' (φ ω)) := by
  subst hP hP'
  exact h k ω

theorem cup_P (hFL : FormLaws) (hFU : FormUniq) (hFC : FormCup) {V : Y.Opens} {P U₁ U₂ : ObjectProperty (Thick (smFun Y q))} (hP : P = inU q V)
    (k₁ : P ≤ U₁) (k₂ : P ≤ U₂) (β₁ : CH.Cn (U₁.ι ⋙ G q 1) 1) (β₂ : CH.Cn (U₂.ι ⋙ G q 1) 1) {a : ℕ}
    (E₂ : Om K (Sec q V) a →ₗ[K] HV q V a a) (E₃ : Om K (Sec q V) (a + 1) →ₗ[K] HV q V (a + 1) (a + 1))
    (h₂ : IsOm q V a E₂) (h₃ : IsOm q V (a + 1) E₃) (g₁ t : Sec q V)
    (hf : ∀ (k₁' : inU q V ≤ U₁) (k₂' : inU q V ≤ U₂), ∃ hz, IsForm q V (a := 1) g₁ ![t]
      ((CH.cx ((inU q V).ι ⋙ G q 1)).cls ((resU (G q 1) k₁').pullC 1 β₁ - (resU (G q 1) k₂').pullC 1 β₂) hz))
    (w : Om K (Sec q V) a →ₗ[Sec q V] Om K (Sec q V) (a + 1))
    (hw : ∀ g₀ (g : Fin a → Sec q V), w (form K g₀ g) = form K g₀ (Fin.cons t g))
    (y : CH.Cn (P.ι ⋙ G q a) a) (hy : CH.d _ a y = 0) (ω : Om K (Sec q V) a)
    (hcls : (CH.cx _).cls y hy = castH (G q a) hP a (E₂ ω))
    (hz : CH.d (P.ι ⋙ G q (a + 1)) (a + 1) ((pairU (grOk (smFun Y q) (Nat.add_comm 1 a)).pair P).cupC (Nat.add_comm 1 a)
      ((resU (G q 1) k₁).pullC 1 β₁ - (resU (G q 1) k₂).pullC 1 β₂) y) = 0) :
    (CH.cx (P.ι ⋙ G q (a + 1))).cls ((pairU (grOk (smFun Y q) (Nat.add_comm 1 a)).pair P).cupC (Nat.add_comm 1 a)
      ((resU (G q 1) k₁).pullC 1 β₁ - (resU (G q 1) k₂).pullC 1 β₂) y) hz =
      castH (G q (a + 1)) hP (a + 1) (E₃ (g₁ • w ω)) := by
  subst hP
  obtain ⟨hb, hform⟩ := hf k₁ k₂
  exact cup_form hFL hFU hFC E₂ E₃ h₂ h₃ g₁ t _ hb hform w hw y hy ω hcls hz

theorem cup_mem_relS {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (P : CH.Pairing F₁ F₂ F₃)
    {Q : ObjectProperty C} (hQ : Cosieve Q) {p n m : ℕ} (h : p + n = m) (b : CH.Cn F₁ p) (x : CH.Cn F₂ n) (hx : x ∈ relS F₂ Q n) :
    P.cupC h b x ∈ relS F₃ Q m := by
  intro s hs
  have hx' : x ((CH.back_mono h).functor ⋙ s) = 0 := hx _ (hQ (s.map (homOfLE (Fin.zero_le _))) hs)
  change P.μ _ _ (CH.term F₂ s x (CH.back h) (CH.back_mono h)) = 0
  unfold CH.term
  rw [hx', map_zero, map_zero]

end Per

end GlobalTheory.CompanionTheory.RelKill
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem kun_res {K : Type} [Field K] (E : XD K) {U₁ U₁' : ObjectProperty E.C₁} {U₂ U₂' : ObjectProperty E.C₂} {U₃ U₃' : ObjectProperty E.D} (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) (h₁' : ∀ T, U₃' T → U₁' (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂' (E.L₂.obj T)) (k₁ : U₁' ≤ U₁) (k₂ : U₂' ≤ U₂) (k₃ : U₃' ≤ U₃) (b₁ : ∀ a n, Function.Bijective ((resU (E.F₁ a) k₁).pull n)) (b₂ : ∀ a n, Function.Bijective ((resU (E.F₂ a) k₂).pull n)) (b₃ : ∀ a n, Function.Bijective ((resU (E.F₃ a) k₃).pull n)) : (E.Kun U₁ U₂ U₃ h₁ h₂ ↔ E.Kun U₁' U₂' U₃' h₁' h₂') :=
  GlobalTheory.T.pairing_iso_of_component_isos (P := fun a => CH.cx (U₁.ι ⋙ E.F₁ a)) (Q := fun a => CH.cx (U₂.ι ⋙ E.F₂ a)) (T := fun a => CH.cx (U₃.ι ⋙ E.F₃ a))
    (P' := fun a => CH.cx (U₁'.ι ⋙ E.F₁ a)) (Q' := fun a => CH.cx (U₂'.ι ⋙ E.F₂ a)) (T' := fun a => CH.cx (U₃'.ι ⋙ E.F₃ a))
    (fun {a a' c} ha => E.pr U₁ U₂ U₃ h₁ h₂ ha) (fun {a a' c} ha => E.pr U₁' U₂' U₃' h₁' h₂' ha)
    (fun a => (resU (E.F₁ a) k₁).hom) (fun a => (resU (E.F₂ a) k₂).hom) (fun a => (resU (E.F₃ a) k₃).hom)
    b₁ b₂ b₃
    (fun ha _ _ _ h x y => GlobalTheory.T.pairing_restrict_compat E h₁ h₂ h₁' h₂' k₁ k₂ k₃ ha h x y)

end GlobalTheory.CompanionTheory.KunGlue
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem amat_map_conj {n : ℕ} (l : Fin n → ℂ) :
    (Formalism.REAL.Amat l).map (starRingEnd ℂ) = Formalism.REAL.Amat (fun a => conj (l a)) := by
  ext a b
  simp only [Matrix.map_apply, Formalism.REAL.Amat, Matrix.of_apply]
  split_ifs <;> simp

theorem conj_gelfVal {n : ℕ} (c : Fin n → ℂ) (m : ℕ) :
    conj (GlobalTheory.Dec.gelfVal c m) = GlobalTheory.Dec.gelfVal (fun a => conj (c a)) m := by
  have h : ((Formalism.REAL.Amat fun a => c a + ((n : ℂ) - 1) / 2) ^ m).map (starRingEnd ℂ) =
      (Formalism.REAL.Amat fun a => conj (c a) + ((n : ℂ) - 1) / 2) ^ m := by
    rw [Matrix.map_pow, amat_map_conj]
    congr 2
    funext a
    simp [map_ofNat]

  simp only [GlobalTheory.Dec.gelfVal, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← h]
  rfl

theorem prod_one_sub_ne_zero {n : ℕ} (l : Fin n → ℂ) :
    (∏ a, (1 - PowerSeries.C (l a) * PowerSeries.X) : PowerSeries ℂ) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun a _ h => ?_
  have := congrArg PowerSeries.constantCoeff h
  simp at this

theorem gser_comp_perm {n : ℕ} (c : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) :
    gser (fun a => c (σ a)) = gser c := by
  have h1 := gser_mul_prod n (fun a => c (σ a))
  have h2 := gser_mul_prod n c
  beta_reduce at h1
  have e1 : (∏ a, (1 - PowerSeries.C (c (σ a) + ((n : ℂ) - 1) / 2) * PowerSeries.X) : PowerSeries ℂ) =
      ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X) :=
    Equiv.prod_comp σ (fun a => (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X))
  have e2 : (∏ a, (1 - PowerSeries.C (c (σ a) + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X) : PowerSeries ℂ) =
      ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X) :=
    Equiv.prod_comp σ (fun a => (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X))
  rw [e1, e2] at h1
  have hP : (∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X) : PowerSeries ℂ) ≠ 0 :=
    prod_one_sub_ne_zero _
  have h3 : (1 - PowerSeries.X * gser (fun a => c (σ a))) = 1 - PowerSeries.X * gser c :=
    mul_right_cancel₀ hP (h1.trans h2.symm)
  have h4 : PowerSeries.X * gser (fun a => c (σ a)) = PowerSeries.X * gser c := sub_right_injective h3
  exact mul_left_cancel₀ PowerSeries.X_ne_zero h4

theorem gelfVal_comp_perm {n : ℕ} (c : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (m : ℕ) :
    GlobalTheory.Dec.gelfVal (fun a => c (σ a)) m = GlobalTheory.Dec.gelfVal c m := by
  have h := congrArg (PowerSeries.coeff m) (gser_comp_perm c σ)
  simpa [gser] using h

theorem conj_gelfVal_of_isHerm : ∀ (n : ℕ) (χ : Inf n), IsHerm χ → ∀ (s : Bool) (m : ℕ),
    conj (GlobalTheory.Dec.gelfVal (χ s) m) = GlobalTheory.Dec.gelfVal (fun a => - χ (!s) a) m := by
  intro n χ hχ s m
  obtain ⟨σ, hσ⟩ := hχ
  rw [conj_gelfVal]
  cases s
  · simp only [Bool.not_false]
    rw [← gelfVal_comp_perm (fun a => conj (χ false a)) σ]
    congr 1
    funext a
    simp [hσ a]
  · simp only [Bool.not_true]
    rw [← gelfVal_comp_perm (fun a => -χ false a) σ]
    congr 1
    funext a
    simp [hσ a]

end GlobalTheory.CompanionTheory.WaveMult
end
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.gelfand_series_shift_identity : ∀ (n : ℕ) (c : Fin n → ℂ), (1 - PowerSeries.X * gser c) * ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X) = ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.gser_mul_prod | exact GlobalTheory.CompanionTheory.WaveMult.gser_mul_prod | (intros; apply GlobalTheory.CompanionTheory.WaveMult.gser_mul_prod <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.cosh_transform_convolution : ∀ (g g' : ℝ → ℝ) (T T' : ℝ) (c : ℂ), IsBump g T → IsBump g' T' → coshT g c * coshT g' c = coshT (gconv g g') c := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.CoshMul.coshT_mul_coshT | exact GlobalTheory.CompanionTheory.WaveMult.CoshMul.coshT_mul_coshT | (intros; apply GlobalTheory.CompanionTheory.WaveMult.CoshMul.coshT_mul_coshT <;> assumption)
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens Filter Topology

namespace GlobalTheory.CompanionTheory.UnrDens

theorem unrFormula : PositivityTheory.PfSWUS.Loc.UnrFormula := by
  intro R _ σ ϖ q ε hR m n hnm S T hS hT
  have hq : (0 : ℝ) < q := by exact_mod_cast lt_trans zero_lt_one hR.one_lt
  have hsq : n ^ 2 ≤ 2 * m * n := by nlinarith
  obtain ⟨a, ha⟩ : ∃ a, 2 * m * n - n ^ 2 = a := ⟨_, rfl⟩
  have ha' : a + n ^ 2 = 2 * m * n := by omega
  have hsol : ∀ j : ℕ, (solCount σ ϖ S T (j + 1) : ℝ) =
      (q : ℝ) ^ a * (∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ)))) * (q : ℝ) ^ (j * a) := by
    intro j
    induction j with
    | zero =>
      rw [GlobalTheory.T.card_unimodular_hermitian_reps_level_one R σ ϖ q ε hR m n hnm S T hS hT, ha]
      simp
    | succ j ih =>
      rw [GlobalTheory.T.unimodular_hermitian_reps_count_succ R σ ϖ q ε hR m n hnm S T hS hT (j + 1) (by omega), ha]
      push_cast
      rw [ih, add_mul, one_mul, pow_add]
      ring
  have hdens : ∀ j : ℕ, densAt σ ϖ S T (j + 1) = ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by
    intro j
    unfold densAt
    have hM : Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ (j + 1))) = q ^ (2 * (j + 1) * (m * n)) := by
      show Nat.card (Fin m → Fin n → R ⧸ lev ϖ (j + 1)) = _
      rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR (j + 1), ← pow_mul,
        ← pow_mul]
      ring_nf
    rw [hsol j, GlobalTheory.T.card_hermitian_matrices_mod_pow R σ ϖ q ε hR n (j + 1), hM]
    have he : a + j * a + (j + 1) * n ^ 2 = 2 * (j + 1) * (m * n) := by
      calc a + j * a + (j + 1) * n ^ 2 = (j + 1) * (a + n ^ 2) := by ring
        _ = (j + 1) * (2 * m * n) := by rw [ha']
        _ = 2 * (j + 1) * (m * n) := by ring
    have hpos : (0 : ℝ) < (q : ℝ) ^ (2 * (j + 1) * (m * n)) := pow_pos hq _
    push_cast
    rw [div_eq_iff hpos.ne', ← he, pow_add, pow_add]
    ring
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact (hdens j).symm

end GlobalTheory.CompanionTheory.UnrDens
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.isUnit_of_isUnit_sharp' : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (a : A.A), IsUnit (A.sharp a) → IsUnit a := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.isUnit_of_isUnit_sharp | exact GlobalTheory.CompanionTheory.Untilt.isUnit_of_isUnit_sharp | (intros; apply GlobalTheory.CompanionTheory.Untilt.isUnit_of_isUnit_sharp <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfAlg

theorem pow_mul_mem_span_iff {R : Type*} [CommRing R] {a : R} (ha : a ∈ nonZeroDivisors R) (n m : ℕ) (x : R) :
    a ^ n * x ∈ Ideal.span {a ^ (n + m)} ↔ x ∈ Ideal.span {a ^ m} := by
  have hn : a ^ n ∈ nonZeroDivisors R := pow_mem ha n
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
    refine Ideal.mem_span_singleton'.2 ⟨c, ?_⟩
    have e : a ^ n * (c * a ^ m) = a ^ n * x := by rw [← hc, pow_add]; ring
    exact sub_eq_zero.1 (mem_nonZeroDivisors_iff_left.1 hn (c * a ^ m - x) (by rw [mul_sub, e, sub_self]))
  · intro h
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
    exact Ideal.mem_span_singleton'.2 ⟨c, by rw [pow_add]; ring⟩

theorem lseq : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n m : ℕ), Function.Surjective (A.red (Nat.le_add_right n m)) ∧ (∀ x : A.Acr (n + m), A.red (Nat.le_add_right n m) x = 0 ↔ x ∈ Ideal.span {(l : A.Acr (n + m)) ^ n}) ∧ (∀ x : A.Acr (n + m), (l : A.Acr (n + m)) ^ n * x = 0 ↔ A.red (Nat.le_add_left m n) x = 0) ∧ ∀ x : A.U, (l : A.U) ^ n * x ∈ Ideal.span {(l : A.U) ^ (n + m)} ↔ x ∈ Ideal.span {(l : A.U) ^ m} := by
  intro l _ A n m
  have hl : (l : A.Acr0) ∈ nonZeroDivisors A.Acr0 := A.acris_torsion_free l (Fact.out : l.Prime).ne_zero
  have mk0 : ∀ (k : ℕ) (y : A.Acr0), A.mkAcr k y = 0 ↔ y ∈ Ideal.span {(l : A.Acr0) ^ k} :=
    fun k y => Ideal.Quotient.eq_zero_iff_mem
  refine ⟨?_, ?_, ?_, fun x => pow_mul_mem_span_iff (GlobalTheory.T.perfectoid_xi_nonZeroDivisor A).1 n m x⟩
  · intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨A.mkAcr _ y, rfl⟩
  · intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change A.red _ (A.mkAcr _ y) = 0 ↔ A.mkAcr _ y ∈ _
    rw [red_mk, mk0]
    constructor
    · intro h
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
      refine Ideal.mem_span_singleton'.2 ⟨A.mkAcr _ c, ?_⟩
      rw [map_mul, map_pow, map_natCast]
    · intro h
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
      obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective c
      have e : A.mkAcr (n + m) (d * (l : A.Acr0) ^ n - y) = 0 := by
        set_option synthInstance.maxHeartbeats 400000 in
          rw [map_sub, map_mul, map_pow, map_natCast]
        exact sub_eq_zero.2 hc
      have e2 := (mk0 _ _).1 e
      have e3 : Ideal.span {(l : A.Acr0) ^ (n + m)} ≤ Ideal.span {(l : A.Acr0) ^ n} :=
        Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_add_right n m))
      have e4 := Ideal.sub_mem _ (Ideal.mul_mem_left _ d (Ideal.mem_span_singleton_self ((l : A.Acr0) ^ n))) (e3 e2)
      rwa [sub_sub_cancel] at e4
  · intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change _ * A.mkAcr _ y = 0 ↔ A.red _ (A.mkAcr _ y) = 0
    rw [red_mk, mk0, ← pow_mul_mem_span_iff hl n m y, ← mk0, map_mul, map_pow, map_natCast]

end GlobalTheory.CompanionTheory.PerfAlg
end
