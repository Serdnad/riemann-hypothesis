module

public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyProjCoordsConvergentCoefficients
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.LetterMap

def coeffMap {K L : Type} [Field K] [Field L] (f : K →+* L) : LaurentSeries K →+* LaurentSeries L where
  toFun g := HahnSeries.map g f
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField in
theorem _root_.GlobalTheory.LetterMap.coeffMap_ofPowerSeries {K L : Type} [Field K] [Field L] (f : K →+* L)
    (g : PowerSeries K) :
    _root_.GlobalTheory.LetterMap.coeffMap f (HahnSeries.ofPowerSeries ℤ K g) =
      HahnSeries.ofPowerSeries ℤ L (PowerSeries.map f g) := by
  ext n
  change f ((HahnSeries.ofPowerSeries ℤ K g).coeff n) = _
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs <;> simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
theorem _root_.GlobalTheory.LetterMap.det_ne_zero (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (K₁ : Type) [Field K₁] :
    _root_.Formalism.L2.Pj.arcDet Dw K₁ ≠ 0 := by
  unfold _root_.Formalism.L2.Pj.arcDet
  rw [Finset.prod_ne_zero_iff]
  intro τ _
  have h : (Matrix.of fun i k ↦
      (MvPolynomial.X ⟨τ, (i, k)⟩ : MvPolynomial (_root_.Formalism.L2.Pj.ArcLt Dw) (LaurentSeries K₁))) =
      (MvPolynomial.rename (Sigma.mk τ)).mapMatrix
        (Matrix.mvPolynomialX (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (LaurentSeries K₁)) := by
    ext i k; simp
  rw [h, ← AlgHom.map_det]
  intro h0
  rw [map_eq_zero_iff _ (MvPolynomial.rename_injective _ sigma_mk_injective)] at h0
  exact Matrix.det_mvPolynomialX_ne_zero _ _ h0

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
theorem _root_.GlobalTheory.LetterMap.num_algebraMap {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {K₁ : Type} [Field K₁]
    (P : MvPolynomial (_root_.Formalism.L2.Pj.ArcLt Dw) (LaurentSeries K₁)) :
    _root_.Formalism.L2.Pj.QAt.arcNum (algebraMap _ (_root_.Formalism.L2.Pj.ArcS Dw K₁) P) = P := by
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (_root_.Formalism.L2.Pj.ArcLt Dw) (LaurentSeries K₁)) (_root_.Formalism.L2.Pj.ArcS Dw K₁)) := by
    unfold _root_.Formalism.L2.Pj.ArcS
    exact IsLocalization.injective _
      (powers_le_nonZeroDivisors_of_noZeroDivisors (_root_.GlobalTheory.LetterMap.det_ne_zero Dw K₁))
  have hex : ∃ Q, algebraMap (MvPolynomial (_root_.Formalism.L2.Pj.ArcLt Dw) (LaurentSeries K₁)) (_root_.Formalism.L2.Pj.ArcS Dw K₁) Q =
      algebraMap _ (_root_.Formalism.L2.Pj.ArcS Dw K₁) P := ⟨P, rfl⟩
  unfold _root_.Formalism.L2.Pj.QAt.arcNum
  rw [dite_eq_left hex]
  exact hinj hex.choose_spec

end GlobalTheory.LetterMap

namespace GlobalTheory

end GlobalTheory
end
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecHol

open Filter Topology GlobalTheory.Specialise GlobalTheory.HolHom GlobalTheory.CoordFamily

theorem ev_comb_factor : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), ∀ lin cst, IsFactor A lin cst → ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ (j : ℕ) [NeZero j] (f : A.V → Conv.halfRing T), IsComb A j (Conv.halfRing T) (fun v => f v) → ∀ w hw la v, Conv.ev T w hw (f (v + A.Pw w la)) = Complex.exp (lin w la v + cst w la) ^ j * Conv.ev T w hw (f v) := by
  intro O _ _ A lin cst hF
  obtain ⟨T₀, h₀⟩ := A.exists_isConvLine
  refine ⟨T₀, fun T hT j _ f hf w hw la v => ?_⟩
  obtain ⟨n, r, α, th, h1, h2⟩ := hf
  have key : ∀ z, Conv.ev T w hw (f z) =
      ∑ i, Conv.ev T w hw ⟨r i, (h1 i).1⟩ * A.Sum j (α i) (th i) w z := by
    intro z
    have hm : ∀ i, A.FSum j (α i) (th i) z ∈ Conv.halfRing T :=
      fun i _ hw' => (AnArc.hasSum_coeff_FSum (h₀.mono hT) (h1 i).2 hw' z).summable
    have hv : ∀ i, Conv.ev T w hw ⟨_, hm i⟩ = A.Sum j (α i) (th i) w z :=
      fun i => Conv.ev_eq_of_hasSum hw _ (AnArc.hasSum_coeff_FSum (h₀.mono hT) (h1 i).2 hw z)
    have e : f z = ∑ i, (⟨r i, (h1 i).1⟩ : Conv.halfRing T) * ⟨_, hm i⟩ := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      exact h2 z

    rw [e, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hv i]
  rw [key, key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hF.sum w la v j (α i) (th i) (h1 i).2]
  ring

theorem of_coords (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H)
    (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B)
    (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ)
    (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ) (hF : IsFactor A lin cst) (N : ℕ) [NeZero N]
    (C : Coords Φ N) :
    ∃ T' ≥ Ψ.T, ∀ w : ℂ, T' < w.im → (∀ z, HolAt (fun v => (Ψ.pi w v).left) z) ∧
      (∀ la v, Ψ.pi w (v + A.Pw w la) = Ψ.pi w v) ∧
      (∀ j z, ⊤ ≤ (Ψ.pi w z).left ⁻¹ᵁ o.t.PP.L.U j → DifferentiableAt ℂ (fun v => Ψ.fr w j v ^ N) z) ∧
      ∀ la v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j →
        Ψ.fr w j v ^ N = (Complex.exp (lin w la v + cst w la) * Ψ.fr w j (v + A.Pw w la)) ^ N := by
  obtain ⟨T₁, hT₁, hC, h₁⟩ := SpecCoord.spec_coords E H D l B bb S s o A y Φ Γ Ψ N C
  obtain ⟨T₂, h₂⟩ := GlobalTheory.ArcPts.exists_formal_convergence _ A
  obtain ⟨T₃, h₃⟩ := ev_comb_factor _ A lin cst hF
  set T := max T₁ (max T₂ T₃) with hT
  have e₁ : T₁ ≤ T := le_max_left _ _
  have e₂ : T₂ ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have e₃ : T₃ ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨T, le_trans hT₁ e₁, fun w hw => ?_⟩
  have hw₁ : T₁ < w.im := e₁.trans_lt hw
  have hwC : C.T < w.im := hC.trans_lt hw₁
  have hwΨ : Ψ.T < w.im := lt_of_le_of_lt hT₁ hw₁
  obtain ⟨hy, -, hval⟩ := h₁ w hw₁
  let f : Fin C.n → A.V → Conv.halfRing T := fun i v => Subalgebra.inclusion (Conv.halfRing_mono (hC.trans e₁)) (C.cf i v)
  have hf : ∀ i, IsComb A N (Conv.halfRing T) (fun v => f i v) := fun i => by
    obtain ⟨n, r, α, th, h, h'⟩ := C.comb i
    exact ⟨n, r, α, th, fun a => ⟨Conv.halfRing_mono (hC.trans e₁) (h a).1, (h a).2⟩, h'⟩
  let c : Fin C.n → A.V → ℂ := fun i v => Conv.ev C.T w hwC (C.cf i v)
  have hcf : ∀ i v, c i v = Conv.ev T w hw (f i v) := fun i v => Conv.ev_congr hwC hw rfl
  have hd : ∀ i, Differentiable ℂ (c i) := fun i => by
    rw [show c i = fun v => Conv.ev T w hw (f i v) from funext (hcf i)]
    exact (h₂ T e₂ N).2 (f i) (hf i) w hw
  have hp : ∀ la v i, c i (v + A.Pw w la) = Complex.exp (lin w la v + cst w la) ^ N * c i v := fun la v i => by
    rw [hcf, hcf]
    exact h₃ T e₃ N (f i) (hf i) w hw la v
  have hfr := (SpecGroup.specPts_group E H D l B bb S s o A y Φ Γ Ψ w hwΨ).2.2.1
  have hex : ∀ v, ∃ x : Sp ℂ ⟶ (o.t.G.hom ⁻¹ᵁ C.U).toScheme, x ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι = (Ψ.pi w v).left := fun v => by
    have hxU : ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ (o.t.G.hom ⁻¹ᵁ C.U) := by
      rw [← Scheme.Hom.comp_preimage, Over.w]
      exact hy
    exact ⟨IsOpenImmersion.lift (o.t.G.hom ⁻¹ᵁ C.U).ι (Ψ.pi w v).left (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hxU (x := p) trivial), IsOpenImmersion.lift_fac _ _ _⟩
  choose x hx using hex
  have hv : ∀ i v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j →
      valR (x v) ((Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j)) ((C.b i).f (fun _ => j)) =
        c i v * Ψ.fr w j v ^ N := fun i v j hj => hval i v (x v) j (hx v) hj
  have hc : ∀ v, HasCoords (x v) C.b fun i => c i v := fun v => hasCoords_powOver o.t.PP.isLB fun j hj => by
    rw [hx] at hj
    exact ⟨((hfr v).1 j hj).unit ^ N, fun i => by simpa using hv i v j hj⟩
  have hi : (o.t.G.hom ∣_ C.U) ≫ C.U.ι = (o.t.G.hom ⁻¹ᵁ C.U).ι ≫ o.t.G.hom := morphismRestrict_ι _ _
  have hy' : ∀ v, x v ≫ (o.t.G.hom ∣_ C.U) = x 0 ≫ (o.t.G.hom ∣_ C.U) := fun v => by
    rw [← cancel_mono C.U.ι, Category.assoc, Category.assoc, hi, ← Category.assoc, ← Category.assoc, hx, hx,
      Over.w, Over.w]
  have hhol : ∀ z, HolAt x z := fun z => holAt_of_coords C.emb hy' hc fun i => hd i z
  have hhol' : ∀ z, HolAt (fun v => (Ψ.pi w v).left) z := fun z => by
    have := (hhol z).comp (o.t.G.hom ⁻¹ᵁ C.U).ι
    simpa only [hx] using this
  have hper : ∀ la v, x v = x (v + A.Pw w la) := fun la v =>
    eq_of_proportional C.emb ((hy' _).trans (hy' _).symm) (hc v) (hc _) (hp la v)
  have hper' : ∀ la v, Ψ.pi w (v + A.Pw w la) = Ψ.pi w v := fun la v =>
    Over.OverMorphism.ext (by rw [← hx, ← hx, ← hper])
  refine ⟨hhol', hper', fun j z hj => ?_, fun la v j hj => ?_⟩
  · obtain ⟨i, hi0⟩ := C.bpf w hwC z
    have hzj : ⊤ ≤ x z ⁻¹ᵁ (Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j) := by
      intro p _
      rw [← hx] at hj
      exact Set.mem_iInter.2 fun _ => hj (x := p) trivial
    have h1 := (hhol z _ hzj).2 ((C.b i).f (fun _ => j))
    have hne : ∀ᶠ v in 𝓝 z, c i v ≠ 0 := (hd i z).continuousAt.eventually_ne hi0
    refine (h1.fun_mul ((hd i z).fun_inv hi0)).congr_of_eventuallyEq
      (((hhol' z _ hj).1.and hne).mono fun v hv' => ?_)
    simp only [valAt'_eq_valR]
    rw [hv i v j hv'.1, mul_comm, inv_mul_cancel_left₀ hv'.2]
  · obtain ⟨i, hi0⟩ := C.bpf w hwC v
    have h1 := hv i v j hj
    have h2 := hv i (v + A.Pw w la) j (by rw [hper']; exact hj)
    rw [← hper, h1, hp] at h2
    apply mul_left_cancel₀ (show c i v ≠ 0 from hi0)
    rw [h2]
    ring

theorem specPts_holomorphic : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), AnFin A → Φ.Rational → ∀ lin cst, IsFactor A lin cst → ∃ T' ≥ Ψ.T, ∀ w : ℂ, T' < w.im → IsHolTo Set.univ (fun v => (Ψ.pi w v).left) ∧ (∀ la, Ψ.pi w (A.Pw w la) = 1) ∧ (∀ j, DifferentiableOn ℂ (Ψ.fr w j) {v | ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j}) ∧ ∀ la v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j → Ψ.fr w j v = Complex.exp (lin w la v + cst w la) * Ψ.fr w j (v + A.Pw w la) := by
  intro hL hL2 E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ Ψ hA hΦ lin cst hF
  obtain ⟨C₄⟩ := GlobalTheory.SpanFrame.nonempty_coords hL hL2 E H D l B bb S s o A y Φ hA hΦ 4 le_rfl
  obtain ⟨C₅⟩ := GlobalTheory.SpanFrame.nonempty_coords hL hL2 E H D l B bb S s o A y Φ hA hΦ 5 (by norm_num)
  obtain ⟨T₄, hT₄, h₄⟩ := of_coords E H D l B bb S s o A y Φ Γ Ψ lin cst hF 4 C₄
  obtain ⟨T₅, -, h₅⟩ := of_coords E H D l B bb S s o A y Φ Γ Ψ lin cst hF 5 C₅
  refine ⟨max T₄ T₅, le_max_of_le_left hT₄, fun w hw => ?_⟩
  have hw₄ : T₄ < w.im := (le_max_left _ _).trans_lt hw
  obtain ⟨hhol, hper, hd₄, hq₄⟩ := h₄ w hw₄
  obtain ⟨-, -, hd₅, hq₅⟩ := h₅ w ((le_max_right _ _).trans_lt hw)
  obtain ⟨hadd, -, hfr, -⟩ := SpecGroup.specPts_group E H D l B bb S s o A y Φ Γ Ψ w (lt_of_le_of_lt hT₄ hw₄)
  have hne : ∀ v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j → Ψ.fr w j v ≠ 0 := fun v j hj => ((hfr v).1 j hj).ne_zero
  refine ⟨isHolTo_of_holAt isOpen_univ fun z _ => hhol z, fun la => ?_, fun j z hz => ?_, fun la v j hj => ?_⟩
  · have h := hper la 0
    rw [hadd] at h
    exact mul_eq_left.1 h
  · refine DifferentiableAt.differentiableWithinAt ?_
    refine ((hd₅ j z hz).fun_mul ((hd₄ j z hz).fun_inv (pow_ne_zero _ (hne z j hz)))).congr_of_eventuallyEq
      ((hhol z _ hz).1.mono fun v hv => ?_)
    have := hne v j hv
    beta_reduce
    field_simp
  · have h := hq₅ la v j hj
    rw [pow_succ _ 4, pow_succ _ 4, ← hq₄ la v j hj] at h
    exact mul_left_cancel₀ (pow_ne_zero _ (hne v j hj)) h

end GlobalTheory.SpecHol
end
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstTerm

section Values

variable {A : Type} [CommRing A] {B B₀ : Scheme.{0}}

theorem valR_zpow (x : Sp A ⟶ B) (U : B.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (t : Γ(B, U)ˣ) (u : Aˣ)
    (hu : (u : A) = valR x U t.val) (n : ℤ) : valR x U (t ^ n).val = ((u ^ n : Aˣ) : A) := by
  have e : u = Units.map (HolHom.evalHom x U h).toMonoidHom t := Units.ext (hu.trans (HolHom.valR_eq x U h _))
  rw [e, ← map_zpow, HolHom.valR_eq x U h]
  rfl

theorem le_div {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀} (x : Sp A ⟶ B) {k : M₀.ι} {m : M.ι}
    (h₀ : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ M₀.U k) (h : ⊤ ≤ x ⁻¹ᵁ M.U m) :
    ⊤ ≤ x ⁻¹ᵁ (LB.div (M₀.pull φ) M).U (fun _ => k, m) :=
  fun _ hz => ⟨Set.mem_iInter.2 fun _ => h₀ hz, h hz⟩

theorem valR_pullGen {A₀ : Type} [CommRing A₀] (ρ : A₀ →+* A) {M₀ : LB B₀} {K : Type} [Fintype K]
    {ψ : K → (Sp A₀ ⟶ B₀)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M₀ ψ ε)) (k : K → M₀.ι)
    (h : ⊤ ≤ (𝟙 (Sp A₀)) ⁻¹ᵁ LB.wchart M₀ ψ k) :
    valR (𝟙 (Sp A)) _ ((LB.pullGen M₀ ψ ε t (spMap ρ)).s k).val = ρ (valR (𝟙 (Sp A₀)) _ (t.s k).val) := by
  have h' : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart M₀ (fun i => spMap ρ ≫ ψ i) k :=
    fun z _ => Set.mem_iInter.2 fun i => Set.mem_iInter.1 (h (show spMap ρ z ∈ (⊤ : (Sp A₀).Opens) from trivial)) i
  refine (HolHom.valR_res (𝟙 (Sp A)) _ _ h').trans ((HolHom.valR_comp (𝟙 (Sp A)) (spMap ρ) _ _).symm.trans ?_)
  refine Eq.trans ?_ (HolHom.valR_spMap ρ (𝟙 (Sp A₀)) _ h _)
  rw [Category.id_comp, Category.comp_id]
  rfl

theorem prod_factors {G : Type} [CommGroup G] (u : Fin 4 → G) (j : ℕ) :
    (∏ i, u i ^ Out.DegPre.famε j i) * ∏ i, ![u 1, u 2, u 0, u 3] i ^ Out.DegPre.gtε i = u 0 ^ j := by
  simp only [Fin.prod_univ_four, Out.DegPre.famε, Out.DegPre.gtε, Matrix.cons_val, zpow_sub, zpow_neg, zpow_one,
    zpow_natCast]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

end Values

section Points

variable {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R) {T : Over (Sp R)} (b : T ⟶ D.P.A) (α : D.X)

theorem comp_famφB (i : Fin 4) : b.left ≫ D.famφB α i = D.gtφT T b α (![2, 0, 1, 3] i) := by
  have h : ∀ p : 𝟙_ (Over (Sp R)) ⟶ D.P.A, b ≫ toUnit D.P.A ≫ p = toUnit T ≫ p := fun p => by
    rw [← Category.assoc, comp_toUnit]
  fin_cases i
  · exact Category.comp_id _
  · change (b ≫ (𝟙 D.P.A * toUnit _ ≫ D.c α)).left = ((toUnit _ ≫ D.c α) * b).left
    rw [MonObj.comp_mul, h, Category.comp_id, mul_comm]
  · exact congrArg (·.left) (h _)
  · exact congrArg (·.left) (h _)

end Points

section Core

open FrameValue

variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {D₀ : Out.DegPre ℂ} {n : ℕ}
  (u : HolUnif D₀.P.A D₀.P.L n) {α₀ : D₀.X} {c : Fin n → ℂ}

theorem toUnit_comp_left {B : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ B) :
    (show Sp ℂ ⟶ _ from (toUnit (Out.TF (R := ℂ) ℂ) ≫ p).left) = p.left := by
  have e : Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ = 𝟙 (Sp ℂ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    exact Spec.map_id _
  change (Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ) ≫ p.left = _
  rw [e]
  exact Category.id_comp _

theorem gtφ_eq (hc : u.ex c = D₀.c α₀) {b₀ : Out.TF (R := ℂ) ℂ ⟶ D₀.P.A} {z : Fin n → ℂ}
    (hb : (show Sp ℂ ⟶ _ from b₀.left) = (u.ex z).left) (k : Fin 4) :
    (show Sp ℂ ⟶ _ from Out.DegPre.gtφ D₀ ℂ b₀ α₀ k) = (u.ex (![c + z, c, z, 0] k)).left := by
  have hb' : b₀ = toUnit _ ≫ u.ex z := Over.OverMorphism.ext (hb.trans (toUnit_comp_left _).symm)
  have h0 : u.ex 0 = η[D₀.P.A] := by
    rw [(u.ker 0).2 (zero_mem _), Hom.one_def, toUnit_unit, Category.id_comp]
  fin_cases k
  · refine Eq.trans ?_ (toUnit_comp_left _)
    change (toUnit _ ≫ D₀.c α₀ * b₀).left = (toUnit _ ≫ u.ex (c + z)).left
    rw [hb', u.ex_add, MonObj.comp_mul, hc]
  · exact (toUnit_comp_left _).trans (congrArg (·.left) hc.symm)
  · exact hb
  · exact (toUnit_comp_left _).trans (congrArg (·.left) h0.symm)


omit [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] in
theorem isLift_famφB (hc : u.ex c = D₀.c α₀) (z : Fin n → ℂ) :
    IsLift u (D₀.famφB α₀) (u.ex z).left ![z, z + c, c, 0] := fun k => by
  have h : ∀ p : 𝟙_ (Over (Sp ℂ)) ⟶ D₀.P.A, u.ex z ≫ toUnit D₀.P.A ≫ p = p := fun p => by
    rw [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  fin_cases k
  · exact Category.comp_id _
  · change (u.ex z ≫ (𝟙 D₀.P.A * toUnit _ ≫ D₀.c α₀)).left = (u.ex (z + c)).left
    rw [MonObj.comp_mul, h, Category.comp_id, u.ex_add, hc]
  · change (u.ex z ≫ toUnit _ ≫ D₀.c α₀).left = (u.ex c).left
    rw [h, hc]
  · change (u.ex z ≫ toUnit _ ≫ η[D₀.P.A]).left = (u.ex 0).left
    rw [h, (u.ker 0).2 (zero_mem _), Hom.one_def, toUnit_unit, Category.id_comp]

theorem core {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I} {S : Type} [CommRing S]
    [IsLocalRing S] (κ : R →+* S) (ρ : ℂ →+* S) {φ : D.toPre.P.A.left ⟶ D₀.P.A.left}
    (w : LB.Iso D.toPre.P.L (D₀.P.L.pull φ)) (g : Out.GtPt D.toPre (Over.mk (spMap κ))) (g₀ : Out.GtPtF D₀ ℂ)
    {α : D.toPre.X} {z : Fin n → ℂ} (hc : u.ex c = D₀.c α₀) (hb : (show Sp ℂ ⟶ _ from g₀.b.left) = (u.ex z).left)
    (hg : GenRelR (A := S) w (g.s α) (LB.pullGen _ _ _ (g₀.s α₀) (spMap ρ))) {j : ℕ} (s₀ : D₀.SecB j α₀)
    (f : D.toPre.SecB j α) (r : R)
    (hf : ∀ (p : Sp S ⟶ D.toPre.P.A.left) (jf : Fin 4 → D.toPre.P.L.ι) (j₀ : Fin 4 → D₀.P.L.ι),
      p ≫ D.toPre.P.A.hom = spMap κ →
      (∀ i, ⊤ ≤ (p ≫ D.toPre.famφB α i) ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => j₀ i, jf i)) →
      ∃ t : Fin 4 → Sˣ, (∀ i, (t i : S) = valR (p ≫ D.toPre.famφB α i) _ (w.s (fun _ => j₀ i, jf i)).val) ∧
        (∏ i, t i ^ Out.DegPre.famε j i : Sˣ) * valR p (LB.wchart D.toPre.P.L (D.toPre.famφB α) jf) (f.f jf) =
          κ r * valR (p ≫ φ) (LB.wchart D₀.P.L (D₀.famφB α₀) j₀) (s₀.f j₀))
    (jM : D.toPre.P.L.ι) (j₀ : D₀.P.L.ι) (jf jt : Fin 4 → D.toPre.P.L.ι) (hj : FormalValue.CohCharts g α jM jf jt)
    (hM : ⊤ ≤ (show Sp S ⟶ _ from g.b.left) ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => j₀, jM)) :
    valR (A := S) g.b.left _ (w.s (fun _ => j₀, jM)).val ^ j *
        (FormalValue.famVal g f jf * FormalValue.coordVal g α jt) =
      κ r * ρ (secVal u D₀.P.isLB s₀ (u.ex z).left ![z, z + c, c, 0] *
        genVal u D₀.P.isLB (g₀.s α₀) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + z, c, z, 0] * u.fr j₀ z ^ j) := by
  have hφ : ∀ k, FormalValue.coordφ g α k ≫ φ = spMap ρ ≫ (u.ex (![c + z, c, z, 0] k)).left := fun k =>
    (hg.1 k).trans (congrArg (spMap ρ ≫ ·) (gtφ_eq u hc hb k))
  have hq : ∀ i, FormalValue.basePt g ≫ D.toPre.famφB α i = FormalValue.coordφ g α (![2, 0, 1, 3] i) :=
    comp_famφB D.toPre g.b α
  have ejf : ∀ i, jf i = jt (![2, 0, 1, 3] i) := fun i => hj.2.2 (.inr (.inl i)) (.inr (.inr _)) (hq i)
  have ejM : jM = jt 2 := hj.2.2 (.inl PUnit.unit) (.inr (.inr 2)) rfl
  have h₀ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ D₀.P.L.U j₀ := by
    intro y _
    obtain rfl : y = spMap ρ (cpt S) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    exact (congrArg (fun q => q (cpt S) ∈ D₀.P.L.U j₀) (hφ 2)).mp (mem_pull.1 (hM trivial).1)
  obtain ⟨k, hk, ek⟩ : ∃ k : Fin 4 → D₀.P.L.ι,
      (∀ i, ⊤ ≤ (u.ex (![c + z, c, z, 0] i)).left ⁻¹ᵁ D₀.P.L.U (k i)) ∧ k 2 = j₀ := by
    refine ⟨![chartAt D₀.P.isLB (u.ex (c + z)).left, chartAt D₀.P.isLB (u.ex c).left, j₀,
      chartAt D₀.P.isLB (u.ex 0).left], fun i => ?_, rfl⟩
    fin_cases i
    exacts [le_chartAt D₀.P.isLB _, le_chartAt D₀.P.isLB _, h₀, le_chartAt D₀.P.isLB _]
  subst ek ejM
  obtain rfl : jf = fun i => jt (![2, 0, 1, 3] i) := funext ejf
  have hd : ∀ i, ⊤ ≤ FormalValue.coordφ g α i ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => k i, jt i) :=
    fun i => le_div _ (hφ i ▸ FormalValue.top_le_comp (hk i) _) (hj.2.1.trans (LB.wchart_le _ _ _ i))
  obtain ⟨t, ht, e₁⟩ := hf (FormalValue.basePt g) (fun i => jt (![2, 0, 1, 3] i)) (fun i => k (![2, 0, 1, 3] i))
    (Over.w g.b) (fun i => by rw [hq i]; exact hd _)
  simp only [hq] at ht
  have lf := isLift_famφB u hc z
  have lg : IsLift u (Out.DegPre.gtφ D₀ ℂ g₀.b α₀) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + z, c, z, 0] :=
    fun i => (Category.id_comp _).trans (gtφ_eq u hc hb i)
  have cf : ⊤ ≤ (u.ex z).left ⁻¹ᵁ D₀.P.L.wchart (D₀.famφB α₀) (fun i => k (![2, 0, 1, 3] i)) := by
    refine (lf.le_iff _).2 fun i => ?_
    fin_cases i
    exacts [hk 2, add_comm c z ▸ hk 0, hk 1, hk 3]
  have cg := (lg.le_iff k).2 hk
  have e₂ : valR (FormalValue.basePt g ≫ φ) _ (s₀.f fun i => k (![2, 0, 1, 3] i)) = _ :=
    (congrArg (fun q => valR q _ (s₀.f fun i => k (![2, 0, 1, 3] i))) (hφ 2)).trans
      ((HolHom.valR_spMap ρ (u.ex z).left _ cf _).trans (congrArg ρ (valAt'_sec D₀.P.isLB s₀ lf cf)))
  have e₃ : FormalValue.coordVal g α jt = _ := (hg.2 jt k hd).trans (congrArg₂ (· * ·)
    (Finset.prod_congr rfl fun i _ => valR_zpow _ _ (hd i) _ (![t 1, t 2, t 0, t 3] i)
      (by fin_cases i; exacts [ht 1, ht 2, ht 0, ht 3]) _)
    ((valR_pullGen ρ (g₀.s α₀) k cg).trans (congrArg ρ (valAt'_gen D₀.P.isLB (g₀.isGen α₀) lg cg))))
  have e₄ : GlobalTheory.FrameValue.frameProd u (Out.DegPre.famε j) ![z, z + c, c, 0] (fun i => k (![2, 0, 1, 3] i)) *
      GlobalTheory.FrameValue.frameProd u Out.DegPre.gtε ![c + z, c, z, 0] k = u.fr (k 2) z ^ j := by
    have n₀ : u.fr (k 0) (c + z) ≠ 0 := u.fr_ne _ _ (hk 0)
    have n₁ : u.fr (k 1) c ≠ 0 := u.fr_ne _ _ (hk 1)
    have n₂ : u.fr (k 2) z ≠ 0 := u.fr_ne _ _ (hk 2)
    have n₃ : u.fr (k 3) 0 ≠ 0 := u.fr_ne _ _ (hk 3)
    delta GlobalTheory.FrameValue.frameProd
    simp only [Fin.prod_univ_four, Out.DegPre.famε, Out.DegPre.gtε, Matrix.cons_val, zpow_sub₀ n₂,
      zpow_neg, zpow_one, zpow_natCast, add_comm z c]
    field_simp
  have e₅ : (t 0 : S) ^ j * ∏ i, ((![t 1, t 2, t 0, t 3] i ^ (-Out.DegPre.gtε i) : Sˣ) : S) =
      ((∏ i, t i ^ Out.DegPre.famε j i : Sˣ) : S) := by
    rw [← Units.coe_prod, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← prod_factors t j]
    simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel_right]
  replace e₁ := e₁.trans (congrArg (κ r * ·) e₂)
  refine (congrArg₂ (fun a b => a ^ j * (_ * b)) (ht 0).symm e₃).trans ?_
  rw [← e₄]
  simp only [map_mul] at e₁ ⊢
  rw [← e₅] at e₁
  unfold FormalValue.famVal
  linear_combination (ρ (genVal u D₀.P.isLB (g₀.s α₀) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + z, c, z, 0]) *
    ρ (GlobalTheory.FrameValue.frameProd u Out.DegPre.gtε ![c + z, c, z, 0] k)) * e₁

end Core

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GlobalTheory.ArcPts.GtAn a) (Ξ : GlobalTheory.ArcPts.ConstPts W Λ) (j : ℕ) (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (f : W.P.D.toPre.SecB j (W.e (Λ.ε α))) (r : ℂ⟦X⟧), (∀ (Z : Type) [CommRing Z] [IsLocalRing Z] (p : Sp Z ⟶ W.P.D.toPre.P.A.left) (κ : ℂ⟦X⟧ →+* Z) (jf : Fin 4 → W.P.D.toPre.P.L.ι) (j₀ : Fin 4 → a.D₀.P.L.ι), p ≫ W.P.D.toPre.P.A.hom = spMap κ → (∀ i, ⊤ ≤ (p ≫ W.P.D.toPre.famφB (W.e (Λ.ε α)) i) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀ i, jf i)) → ∃ u : Fin 4 → Zˣ, (∀ i, (u i : Z) = valR (p ≫ W.P.D.toPre.famφB (W.e (Λ.ε α)) i) _ (W.w.s (fun _ => j₀ i, jf i)).val) ∧ (∏ i, u i ^ Out.DegPre.famε j i : Zˣ) * valR p (LB.wchart W.P.D.toPre.P.L (W.P.D.toPre.famφB (W.e (Λ.ε α))) jf) (f.f jf) = κ r * valR (p ≫ W.φ) (LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) j₀) (s₀.f j₀)) → ∀ v jM j₀ jf jt, FormalValue.CohCharts (Ξ.g v) (W.e (Λ.ε α)) jM jf jt → ⊤ ≤ (Ξ.g v).b.left ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) → valR (A := ℂ⟦X⟧) (Ξ.g v).b.left _ (W.w.s (fun _ => j₀, jM)).val ^ j * (FormalValue.famVal (Ξ.g v) f jf * FormalValue.coordVal (Ξ.g v) (W.e (Λ.ε α)) jt) = r * PowerSeries.C (Λ.fn j α s₀ v.2 * eTwoPi (v.1 α) * Λ.u.fr j₀ v.2 ^ j) := by
  intro _ _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ j α s₀ f r hf v jM j₀ jf jt hj hM
  have h := core Λ.u (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) (PowerSeries.C (R := ℂ)) W.w (Ξ.g v) (Λ.ex0 v) (Λ.ct α) (Λ.ex0_b v)
    (Ξ.g_rel v (Λ.ε α)) s₀ f r (fun p => hf _ p _) jM j₀ jf jt hj hM
  rw [Λ.arcDict_expZero_section v α] at h
  exact h

end GlobalTheory.ConstTerm
end
end
