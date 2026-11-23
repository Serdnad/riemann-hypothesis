module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle038
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle022
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlaces
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle037
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle023
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle011
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle034
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Flow

theorem map_eq_of_conj {G H : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [MeasurableSpace H] [BorelSpace H] (e : G ≃+ H) (he : Continuous e) (hs : Continuous e.symm)
    (L : G → G) (L' : H → H) (hL' : Continuous L') (hc : ∀ X, e (L X) = L' (e X)) (c : ℝ≥0∞)
    (hH : ∀ ν : Measure H, ν.IsAddHaarMeasure → ν.map L' = c • ν)
    (μ : Measure G) [μ.IsAddHaarMeasure] : μ.map L = c • μ := by
  have hL : Continuous L := by
    have : L = fun X => e.symm (L' (e X)) := by
      funext X; rw [← hc, AddEquiv.symm_apply_apply]
    rw [this]
    exact hs.comp (hL'.comp he)
  have hν := hH (μ.map e) (e.isAddHaarMeasure_map μ he hs)
  have h1 : (μ.map L).map e = (c • μ).map e := by
    rw [Measure.map_map he.measurable hL.measurable, Measure.map_smul c he.measurable.aemeasurable, ← hν,
      Measure.map_map hL'.measurable he.measurable]
    congr 1
    funext X
    exact hc X
  have h2 : ((μ.map L).map e).map e.symm = ((c • μ).map e).map e.symm := by rw [h1]
  rw [Measure.map_map hs.measurable he.measurable, Measure.map_map hs.measurable he.measurable] at h2
  have hid : (e.symm ∘ e : G → G) = id := by funext X; simp
  rwa [hid, Measure.map_id, Measure.map_id] at h2

section Coord

variable {F E A : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A]

def coordEquiv {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) :
    (Fin n → Fin M → A ⊗[F] E) ≃+ (Fin n × Fin M × Fin d → A) where
  toFun X p := (Algebra.TensorProduct.basis A b).repr (X p.1 p.2.1) p.2.2
  invFun Y a i := (Algebra.TensorProduct.basis A b).equivFun.symm (fun k => Y (a, i, k))
  left_inv X := by
    funext a i
    have := (Algebra.TensorProduct.basis A b).equivFun.symm_apply_apply (X a i)
    simpa using this
  right_inv Y := by
    funext ⟨a, i, k⟩
    have := (Algebra.TensorProduct.basis A b).equivFun.apply_symm_apply (fun k => Y (a, i, k))
    exact congrFun this k
  map_add' X Y := by
    funext p
    simp

theorem coordEquiv_smul {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) (a : A)
    (X : Fin n → Fin M → A ⊗[F] E) :
    coordEquiv b n M ((a ⊗ₜ[F] (1 : E)) • X) = fun p => a * coordEquiv b n M X p := by
  funext p
  have h : (a ⊗ₜ[F] (1 : E)) * X p.1 p.2.1 = a • X p.1 p.2.1 := by
    rw [Algebra.smul_def]; rfl
  simp [coordEquiv, h]

end Coord

theorem modulus_flow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (n M : ℕ) (μ : Measure (Fin n → Fin M → AF F ⊗[F] E)), μ.IsAddHaarMeasure → ∀ x : ℝ, μ.map (fun X => ((τ (Multiplicative.ofAdd (x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • X) = ENNReal.ofReal (Real.exp (-(2 * Module.finrank ℚ F * n * M * x))) • μ := by
  intro F E _ _ _ _ _ σ hcm τ hτ n M μ hμ x
  obtain ⟨⟨hAlc, hAsc, hAt2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hAlc
  haveI := hAsc
  haveI := hAt2
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  obtain ⟨hTR, -, -, -, -, -, hHom, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)
  haveI := hTR
  haveI := hBor n M
  have hd : Module.finrank F E = 2 := hcm.2.2.1
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hd
  obtain ⟨-, θ, hθ, hτx⟩ := hτ
  have hh := hHom 2 b
  let hm := hh.homeomorph
  have he : Continuous (coordEquiv (A := AF F) b n M) := by
    refine continuous_pi fun p => ?_
    have h1 : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E => X p.1 p.2.1 :=
      (continuous_apply p.2.1).comp (continuous_apply p.1)
    exact (continuous_apply p.2.2).comp (hh.continuous.comp h1)
  have hs : Continuous (coordEquiv (A := AF F) b n M).symm := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    have h1 : Continuous fun Y : Fin n × Fin M × Fin 2 → AF F => fun k => Y (a, i, k) :=
      continuous_pi fun k => continuous_apply _
    have h2 : (fun Y : Fin n × Fin M × Fin 2 → AF F => (coordEquiv (A := AF F) b n M).symm Y a i) =
        fun Y => hm.symm (fun k => Y (a, i, k)) := by
      funext Y
      apply hm.injective
      rw [Homeomorph.apply_symm_apply]
      funext k
      have := (Algebra.TensorProduct.basis (AF F) b).equivFun.apply_symm_apply (fun k => Y (a, i, k))
      exact congrFun this k
    rw [h2]
    exact hm.symm.continuous.comp h1
  have ht : 0 < Real.exp x := Real.exp_pos x
  refine map_eq_of_conj (coordEquiv (A := AF F) b n M) he hs _
    (fun y p => (show AF F from (θ (Real.exp x), 1)) * y p) ?_ ?_ _ ?_ μ
  · exact continuous_pi fun p => continuous_const.mul (continuous_apply p)
  · intro X
    rw [hτx x]
    exact coordEquiv_smul b n M _ X
  · intro ν hν
    have := GlobalTheory.CompanionTheory.AdelicFlow.map_scalar F hcm.1 θ hθ (Fin n × Fin M × Fin 2) ν (Real.exp x) ht
    rw [this]
    congr 2
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    simp only [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring

end GlobalTheory.CompanionTheory.SW.Flow
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GoodTrans

theorem transit_ring {T : Type} [CommRing T] (O : Subring T) (s : T →+* T)
    (hs : ∀ y ∈ O, s y ∈ O) (hss : ∀ y, s (s y) = y) {M : ℕ} (JT : Matrix (Fin M) (Fin M) T)
    (hJO : ∀ i j, JT i j ∈ O) (hJ : ∀ i j, s (JT j i) = JT i j) (x y : Fin M → T)
    (hx : ∀ i, x i ∈ O) (hy : ∀ i, y i ∈ O) (hxy : hform s JT x x = hform s JT y y)
    (w : T) (hw : w ∈ O) (hxw : hform s JT x x * w = 1)
    (hgood : ∀ p β : O, IsUnit β → s β = β → ∃ ε z : O,
      (ε : T) * s ε = 1 ∧ ((β : T) - s ε * p) * z = 1) :
    ∃ g ∈ UJ s JT, (g : Matrix (Fin M) (Fin M) T) *ᵥ x = y ∧
      (∀ i j, (g : Matrix (Fin M) (Fin M) T) i j ∈ O) ∧
      ∀ i j, ((g⁻¹ : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) i j ∈ O := by
  let τ : O →+* O := s.restrict O O hs
  have hτ : ∀ a : O, ((τ a : O) : T) = s a := fun a => rfl
  let JO : Matrix (Fin M) (Fin M) O := fun i j => ⟨JT i j, hJO i j⟩
  let x0 : Fin M → O := fun i => ⟨x i, hx i⟩
  let y0 : Fin M → O := fun i => ⟨y i, hy i⟩
  have hcoe : ∀ p q : Fin M → O, ((hform τ JO p q : O) : T) =
      hform s JT (fun i => (p i : T)) (fun i => (q i : T)) := by
    intro p q
    simp [hform, hτ, JO]
  have hβ0 : ((hform τ JO x0 x0 : O) : T) = hform s JT x x := hcoe x0 x0
  have hxy0 : hform τ JO x0 x0 = hform τ JO y0 y0 := Subtype.ext (by
    rw [hβ0, hxy]; exact (hcoe y0 y0).symm)
  have hunit : IsUnit (hform τ JO x0 x0) :=
    IsUnit.of_mul_eq_one ⟨w, hw⟩ (Subtype.ext (by
      rw [Subring.coe_mul, hβ0]; exact hxw))
  have hτinv : ∀ a : O, τ (τ a) = a := fun a => Subtype.ext (hss a)
  have hJ0 : ∀ i j, τ (JO j i) = JO i j := fun i j => Subtype.ext (hJ i j)
  have hfix : s (hform τ JO x0 x0 : O) = (hform τ JO x0 x0 : O) := by
    have := GlobalTheory.CompanionTheory.SW.QuasiRefl.hform_conj_symm hτinv hJ0 x0 x0
    exact congrArg Subtype.val this
  obtain ⟨ε, z, hε, hz⟩ := hgood (hform τ JO y0 x0) _ hunit hfix
  have hε' : ε * τ ε = 1 := Subtype.ext hε
  have hu : IsUnit (hform τ JO x0 x0 - τ ε * hform τ JO y0 x0) :=
    IsUnit.of_mul_eq_one z (Subtype.ext hz)
  obtain ⟨g0, hg0, hgx, -⟩ := GlobalTheory.CompanionTheory.SW.QuasiRefl.exists_unitary_carry O τ hτinv M JO hJ0 x0 y0 ε
    hxy0 hunit hε' hu
  have hval : ∀ g : GL (Fin M) O, ((bc O.subtype g : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) =
      (g : Matrix (Fin M) (Fin M) O).map O.subtype := fun g => rfl
  refine ⟨bc O.subtype g0, ?_, ?_, ?_, ?_⟩
  · have h0 : cT τ (g0 : Matrix (Fin M) (Fin M) O) * JO * (g0 : Matrix (Fin M) (Fin M) O) = JO := hg0
    have h1 := congrArg (RingHom.mapMatrix O.subtype) h0
    rw [map_mul, map_mul] at h1
    show cT s ((bc O.subtype g0 : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) * JT *
      ((bc O.subtype g0 : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) = JT
    have e1 : RingHom.mapMatrix O.subtype (cT τ (g0 : Matrix (Fin M) (Fin M) O)) =
        cT s ((bc O.subtype g0 : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) := by
      ext i j
      rfl
    have e2 : RingHom.mapMatrix O.subtype JO = JT := by
      ext i j
      rfl
    have e3 : RingHom.mapMatrix O.subtype (g0 : Matrix (Fin M) (Fin M) O) =
        ((bc O.subtype g0 : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) := rfl
    rwa [e1, e2, e3] at h1
  · funext i
    have := congrArg Subtype.val (congrFun hgx i)
    simpa [Matrix.mulVec, dotProduct, hval, x0, y0] using this
  · intro i j
    rw [hval]
    exact ((g0 : Matrix (Fin M) (Fin M) O) i j).2
  · intro i j
    rw [← map_inv, hval]
    exact (((g0⁻¹ : GL (Fin M) O) : Matrix (Fin M) (Fin M) O) i j).2

theorem mem_latV_iff {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d n M : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) (X : Fin n → Fin M → Fv F v ⊗[F] E) :
    X ∈ latV b v ↔ ∀ a i, X a i ∈ O :=
  ⟨fun h a i => (hO _).2 (h a i), fun h a i => (hO _).1 (h a i)⟩

theorem mulVec_mem {T : Type} [CommRing T] (O : Subring T) {M : ℕ} (g : Matrix (Fin M) (Fin M) T)
    (hg : ∀ i j, g i j ∈ O) (x : Fin M → T) (hx : ∀ i, x i ∈ O) (i : Fin M) : (g *ᵥ x) i ∈ O := by
  simp only [Matrix.mulVec, dotProduct]
  exact O.sum_mem fun j _ => O.mul_mem (hg i j) (hx j)

theorem good_trans : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ x y : Fin 1 → Fin M → Fv F v ⊗[F] E, x ∈ latV b v → y ∈ latV b v → gramR (Fv F v) σ J x = (hermScal (Fv F v) σ (algebraMap F _ t) : HermR (Fv F v) σ 1) → gramR (Fv F v) σ J y = gramR (Fv F v) σ J x → ∃ h : HA (Fv F v) σ J, actW (Fv F v) σ J h x = y ∧ ∀ (n : ℕ) (X : Fin n → Fin M → Fv F v ⊗[F] E), actW (Fv F v) σ J h X ∈ latV b v ↔ X ∈ latV b v := by
  intro F E _ _ _ _ _ σ h M J hJ t ht d b
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have I := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ h d b
  filter_upwards [GlobalTheory.CompanionTheory.SW.GoodRing.good_ring F E σ h d b, I.2 t ht,
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => I.1 (J i j)] with v hring hv hJv
  obtain ⟨O, hO, hstab, -, -, -, hgood, -⟩ := hring
  intro x y hx hy hxt hyx
  have hss : ∀ z : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      show a ⊗ₜ[F] σ (σ e) = a ⊗ₜ[F] e
      rw [hinv]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]
  have hc : ∀ c : Fv F v, c ∈ v.adicCompletionIntegers F → c ⊗ₜ[F] (1 : E) ∈ O := by
    intro c hcv
    refine (hO _).2 fun k => ?_
    have e : c ⊗ₜ[F] (1 : E) = c • (1 : Fv F v ⊗[F] E) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem hcv ((hO 1).1 O.one_mem k)
  set c : Fv F v := algebraMap F (Fv F v) t with hcdef
  have hc0 : c ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  have hβ : hform (sigR (Fv F v) σ) (JR (Fv F v) J) (x 0) (x 0) = c ⊗ₜ[F] (1 : E) :=
    congrFun (congrFun hxt 0) 0
  have hxy : hform (sigR (Fv F v) σ) (JR (Fv F v) J) (x 0) (x 0) =
      hform (sigR (Fv F v) σ) (JR (Fv F v) J) (y 0) (y 0) :=
    (congrFun (congrFun hyx 0) 0).symm
  have hci : c⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
  have hmul : c ⊗ₜ[F] (1 : E) * c⁻¹ ⊗ₜ[F] (1 : E) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hc0, mul_one,
      Algebra.TensorProduct.one_def]
  obtain ⟨g, hg, hgx, hgO, hgiO⟩ := transit_ring O (sigR (Fv F v) σ) hstab hss (JR (Fv F v) J)
    (fun i j => (hO _).2 (hJv i j))
    (fun i j => by
      show sigR (Fv F v) σ (inclR (Fv F v) (J j i)) = inclR (Fv F v) (J i j)
      rw [← hJ.1 i j]
      rfl)
    (x 0) (y 0) (fun i => (hO _).2 (hx 0 i)) (fun i => (hO _).2 (hy 0 i)) hxy
    (c⁻¹ ⊗ₜ[F] (1 : E)) (hc _ hci) (by rw [hβ, hmul]) hgood
  let h' : HA (Fv F v) σ J := (⟨g, hg⟩ : HR (Fv F v) σ J)
  have hact : ∀ {n : ℕ} (X : Fin n → Fin M → Fv F v ⊗[F] E) (a : Fin n),
      actW (Fv F v) σ J h' X a = (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ X a :=
    fun _ _ => rfl
  refine ⟨h', ?_, fun n X => ?_⟩
  · funext a
    rw [hact, Fin.fin_one_eq_zero a, hgx]
  · rw [mem_latV_iff b v O hO, mem_latV_iff b v O hO]
    constructor
    · intro hX a i
      have e : X a = ((g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ
          ((g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ X a) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rw [e]
      exact mulVec_mem O _ hgiO _ (fun j => by rw [← hact]; exact hX a j) i
    · intro hX a i
      rw [hact]
      exact mulVec_mem O _ hgO _ (hX a) i

end GlobalTheory.CompanionTheory.SW.GoodTrans
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FibreInv

theorem map_actW_fibre : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (h : HA R σ J) (S : HermR R σ n), (m S).map (actW R σ J h) = m S := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm h S
  have hR' := hR
  obtain ⟨_, _, _, _, -, -, -, -⟩ := hR'
  obtain ⟨_, _, _, _, -, -, -, hbor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  have hbor' := hbor n M
  obtain ⟨_, _, _, _, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  obtain ⟨g, hgc, hgf⟩ := hlift M J hJ
  obtain ⟨_, -, -, -, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ R
  obtain ⟨hcont, hone, hmul, hgr⟩ := hact n
  have hcg : ∀ k : HA R σ J, Continuous (actW R σ J k : (Fin n → Fin M → R ⊗[F] E) → _) := fun k =>
    hcont.comp (Continuous.prodMk_right k)
  let e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := actW R σ J h
      invFun := actW R σ J h⁻¹
      left_inv := fun X => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun X => by rw [← hmul, mul_inv_cancel, hone]
      continuous_toFun := hcg h
      continuous_invFun := hcg h⁻¹ }
  let B : Set (HermR R σ n) := {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}
  have hB : IsOpen B := by
    have hop := (GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ R hR).isOpen_range
    have hBe : B = (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
        Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext T
      simp [B, IsUnit]
    rw [hBe]
    exact hop.preimage (Continuous.matrix_det continuous_subtype_val)
  have hU : {X | IsUnit (gramR R σ J X).det} = g ⁻¹' B := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_preimage, B, hgf]
  have hm' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (g ⁻¹' B) ν B m := by
    rw [← hU]
    exact hm
  have hgi : ∀ X, g (e X) = (Homeomorph.refl (HermR R σ n)) (g X) := by
    intro X
    apply Subtype.ext
    show (g (actW R σ J h X) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = g X
    rw [← hgf, ← hgf, hgr]
  have ht := GlobalTheory.CompanionTheory.SW.isFibreFamily_transport _ (HermR R σ n) _ μ ν (gramR R σ J) g Subtype.val
    Subtype.val_injective hgc hgf _ (gramR R σ J) g hgc hgf e (Homeomorph.refl _) hgi B hB m hm'
  have himg : (Homeomorph.refl (HermR R σ n)) '' B = B := by simp
  have hνm : ν.map (Homeomorph.refl (HermR R σ n)) = ν := by
    simpa using Measure.map_id (μ := ν)
  have hμm : μ.map e = μ := GlobalTheory.T.unitary_action_preserves_haar_local F E σ hσ M J hJ R hR n μ hμ h
  rw [himg, hνm, hμm, ← hU] at ht
  exact (GlobalTheory.T.gram_fiber_measures_unique F E σ hσ M J hJ R hR n μ ν _ hμ hν ht m hm S)

end GlobalTheory.CompanionTheory.SW.FibreInv
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LocIsom

theorem fibre_map_isometry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (μ' : Measure (Fin n → Fin M → R ⊗[F] E)) m', μ'.IsAddHaarMeasure → IsGramFib R σ J' n μ' ν m' → ∀ g : GL (Fin M) (R ⊗[F] E), JR R J' = cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) → ∀ a : ℝ≥0, μ'.map (actTup R g) = a • μ → ∀ S, (m' S).map (actTup R g) = a • m S := by
  intro F E _ _ _ _ _ σ hcm M J hJ J' hJ' R _ _ _ _ _ hR n μ ν m hμ hν hm μ' m' hμ' hm' g hg a ha S
  have hR' := hR
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := hR'
  obtain ⟨hK1, hK2, hK3, hK4, -, -, -, hK8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  haveI := hK8 n M
  obtain ⟨hH1, hH2, hH3, hH4, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hcm R n
  obtain ⟨l, hlc, hl⟩ := hlift M J hJ
  obtain ⟨l', hlc', hl'⟩ := hlift M J' hJ'
  have hact : ∀ X, gramR R σ J (actTup R g X) = gramR R σ J' X :=
    (GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hcm M J hJ R n).2.2.2.2 J' g hg
  have hcont : ∀ h : GL (Fin M) (R ⊗[F] E),
      Continuous (actTup R h : (Fin n → Fin M → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E)) := by
    intro h
    refine continuous_pi fun b => ?_
    exact continuous_const.matrix_mulVec (continuous_apply b)
  let e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := actTup R g
      invFun := actTup R g⁻¹
      left_inv := fun X => by
        funext b
        simp [actTup, Matrix.mulVec_mulVec]
      right_inv := fun X => by
        funext b
        simp [actTup, Matrix.mulVec_mulVec]
      continuous_toFun := hcont g
      continuous_invFun := hcont g⁻¹ }
  have he : (e : (Fin n → Fin M → R ⊗[F] E) → _) = actTup R g := rfl
  let B : Set (HermR R σ n) := {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}
  have hB : IsOpen B := by
    have hu := (GlobalTheory.T.units_open_embedding_local_tensor F E σ hcm R hR).isOpen_range
    have hd : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have := hu.preimage hd
    convert this using 1
    ext S
    simp [B, IsUnit]
  have hset : {X | IsUnit (gramR R σ J X).det} = l ⁻¹' B := by
    ext X
    simp [B, hl X]
  have hset' : {X | IsUnit (gramR R σ J' X).det} = l' ⁻¹' B := by
    ext X
    simp [B, hl' X]
  have hm'' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ' (gramR R σ J') Subtype.val (l' ⁻¹' B) ν B m' := by
    have := hm'
    unfold IsGramFib at this
    rw [hset'] at this
    exact this
  have hcompat : ∀ X, l (e X) = (Homeomorph.refl _) (l' X) := by
    intro X
    apply Subtype.ext
    show ((l (e X) : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = (l' X : HermR R σ n)
    rw [← hl, ← hl']
    exact hact X
  have hT := GlobalTheory.CompanionTheory.SW.isFibreFamily_transport _ _ _ μ' ν (gramR R σ J') l' Subtype.val
    Subtype.val_injective hlc' hl' _ (gramR R σ J) l hlc hl e (Homeomorph.refl _) hcompat B hB m' hm''
  have himg : (Homeomorph.refl (HermR R σ n)) '' B = B := by simp
  have hνm : ν.map (Homeomorph.refl (HermR R σ n)) = ν := by
    simp
  rw [himg, hνm, he, ha, ← hset] at hT
  have hfib : IsGramFib R σ J n (a • μ) ν (fun S => (m' S).map (actTup R g)) := hT
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    have h0 : μ' ≠ 0 := by
      intro h
      have := isOpen_univ.measure_pos μ' Set.univ_nonempty
      simp [h] at this
    apply h0
    rw [← he] at ha
    have := congrArg (fun ρ : Measure _ => ρ Set.univ) ha
    simp only [Measure.coe_zero, Pi.zero_apply] at this
    rw [Measure.map_apply e.continuous.measurable MeasurableSet.univ] at this
    simpa using this
  have hHaar : (a • μ).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul μ ha0
  have h1 := GlobalTheory.T.gram_fiber_measures_scaling F E σ hcm M J hJ R hR n μ ν m hμ hν hm a 1 ha0 one_ne_zero
  rw [one_smul] at h1
  simp only [div_one] at h1
  exact GlobalTheory.T.gram_fiber_measures_unique F E σ hcm M J hJ R hR n (a • μ) ν _ hHaar hν hfib _ h1 S

end GlobalTheory.CompanionTheory.SW.LocIsom
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.euler_product_measure_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : ℝ≥0) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsEulerProd b I c minf m → ∀ (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable φinf → (∀ v, MeasurableSet (A v)) → (∀ v, m v (A v) < ⊤) → (∀ᶠ v in Filter.cofinite, A v = latV b v) → Multipliable (fun v => (m v (A v)).toReal) ∧ ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A v}, φinf (projInf X) ∂I = (c : ℝ≥0∞) * (∫⁻ X, φinf X ∂minf) * ENNReal.ofReal (∏' v, (m v (A v)).toReal) := by
  first | exact @GlobalTheory.CompanionTheory.SW.EulerBox.euler_box | exact GlobalTheory.CompanionTheory.SW.EulerBox.euler_box | (intros; apply GlobalTheory.CompanionTheory.SW.EulerBox.euler_box <;> assumption)
end
