module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableParabolic
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle404
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermUnipotentIntegralVariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle240
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle001
import GroundTheory.GlobalFields.Adele.Topology
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle528
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle544
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle008
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.SliceClasses

theorem E_lift {X Y : Type*} (L : ℝ → (X → ℂ) →ₗ[ℂ] (X → ℂ)) (L' : ℝ → (Y → ℂ) →ₗ[ℂ] (Y → ℂ))
    (hL0 : ∀ f, L 0 f = f) (hLL : ∀ s t f, L s (L t f) = L (t + s) f) (f₀ : X → ℂ)
    [FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun t => L t f₀))] (B : (X → ℂ) → (Y → ℂ))
    (hadd : ∀ v ∈ Submodule.span ℂ (Set.range fun t => L t f₀), ∀ w ∈ Submodule.span ℂ (Set.range fun t => L t f₀),
      B (v + w) = B v + B w)
    (hsmul : ∀ (a : ℂ), ∀ w ∈ Submodule.span ℂ (Set.range fun t => L t f₀), B (a • w) = a • B w)
    (c d : ℂ) (hB : ∀ t : ℝ, ∀ w ∈ Submodule.span ℂ (Set.range fun t => L t f₀),
      B (L t w) = Complex.exp (d * t) • L' t (B w))
    (F' : Y → ℂ) (hF' : F' ∈ Submodule.span ℂ (Set.range fun t => L' t (B f₀))) (hne : F' ≠ 0)
    (heig : ∀ t : ℝ, L' t F' = Complex.exp (c * t) • F') :
    ∃ F ∈ Submodule.span ℂ (Set.range fun t => L t f₀), F ≠ 0 ∧
      ∀ t : ℝ, L t F = Complex.exp ((c + d) * t) • F := by
  set W := Submodule.span ℂ (Set.range fun t => L t f₀) with hWdef
  have hf₀ : f₀ ∈ W := by
    have h0 : L 0 f₀ ∈ W := Submodule.subset_span ⟨0, rfl⟩
    rwa [hL0] at h0
  have hW : ∀ t, ∀ w ∈ W, L t w ∈ W := by
    intro t w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      rw [hLL]
      exact Submodule.subset_span ⟨u + t, rfl⟩
    | zero => rw [map_zero]; exact W.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact W.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact W.smul_mem a hx
  have hL : ∀ s t, ∀ w ∈ W, L s (L t w) = L t (L s w) := fun s t w _ => by rw [hLL, hLL, add_comm]
  have hB0 : B 0 = 0 := by
    have := hsmul 0 0 W.zero_mem
    rwa [zero_smul, zero_smul] at this
  have key : ∀ x ∈ Submodule.span ℂ (Set.range fun t => L' t (B f₀)), ∃ w ∈ W, B w = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      refine ⟨Complex.exp (-(d * t)) • L t f₀, W.smul_mem _ (Submodule.subset_span ⟨t, rfl⟩), ?_⟩
      rw [hsmul _ _ (Submodule.subset_span ⟨t, rfl⟩), hB t f₀ hf₀, smul_smul, ← Complex.exp_add, neg_add_cancel,
        Complex.exp_zero, one_smul]
    | zero => exact ⟨0, W.zero_mem, hB0⟩
    | add x y _ _ hx hy =>
      obtain ⟨v, hv, rfl⟩ := hx
      obtain ⟨w, hw, rfl⟩ := hy
      exact ⟨v + w, W.add_mem hv hw, hadd v hv w hw⟩
    | smul a x _ hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      exact ⟨a • v, W.smul_mem a hv, hsmul a v hv⟩
  obtain ⟨w₀, hw₀, hBw₀⟩ := key F' hF'
  exact eig_lift W L hL hW L' B hadd hsmul c d hB w₀ hw₀ (hBw₀ ▸ hne) (hBw₀ ▸ heig)

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def E_vol (E : Type) [Field E] [NumberField E] (N r : ℕ) : ℂ :=
  (((unipMeasure E N r).real (unipFundamentalDomain E N r) : ℝ) : ℂ)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem E_vol_ne (N r : ℕ) : E_vol E N r ≠ 0 := by
  have := JDict.vol_pos E N r
  unfold E_vol
  exact_mod_cast this.ne'

omit [_root_.NumberField.IsTotallyComplex E] in
theorem E_ctn_eq {N : ℕ} (r : ℕ) (u : GA E N → ℂ) (g : GA E N) :
    An.ctn r u g = (E_vol E N r)⁻¹ * constantTerm r u g := rfl

omit [_root_.NumberField.IsTotallyComplex E] in
theorem E_ct_eq {N : ℕ} (r : ℕ) (u : GA E N → ℂ) (g : GA E N) :
    constantTerm r u g = E_vol E N r * An.ctn r u g := by
  rw [E_ctn_eq, ← mul_assoc, mul_inv_cancel₀ (E_vol_ne N r), one_mul]

theorem E_cont_ctn {N : ℕ} (r : ℕ) {u : GA E N → ℂ} (hc : Continuous u)
    (hl : ∀ γ g, u (ratGL E N γ * g) = u g) : Continuous (An.ctn r u) := by
  have : BorelSpace (BlockIx N r → Ad E) := ⟨JDict.pi_eq_borel E N r⟩
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E N r
  have hfin : unipMeasure E N r (unipFundamentalDomain E N r) ≠ ⊤ := by
    obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := E) (n := N) (r := r)
    exact ((measure_mono hDC).trans_lt hC.measure_lt_top).ne
  have h := GlobalTheory.CompanionTheory.CuspL2.continuous_constTerm (unipMeasure E N r) hfin hK hcov hc hl
  refine continuous_const.mul ?_
  convert h using 2 with g
  simp only [constantTerm, GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip]

theorem E_cont_span {N : ℕ} (r : ℕ) {f : GA E N → ℂ} (hf : Continuous f) :
    ∀ w ∈ Submodule.span ℂ (Set.range fun t : ℝ => fun g => f (aT E N r t * g)), Continuous w := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    exact hf.comp (continuous_const.mul continuous_id)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact continuous_const.smul hx

def E_B {N : ℕ} {Y ι : Type*} [Fintype ι] (P : (ι → Ad E) → GA E N) (Q : ℝ → Y → GA E N) (κ : ℂ) (τs : Finset ℝ)
    (a : ℝ → ℂ) (f : GA E N → ℂ) (m : Y) : ℂ :=
  κ * ∑ t ∈ τs, a t * ∫ b, f (P b * Q t m) ∂(Measure.pi fun _ : ι => boxMeasure E)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem E_B_add {N : ℕ} {Y ι : Type*} [Fintype ι] {P : (ι → Ad E) → GA E N} (hP : Continuous P) (Q : ℝ → Y → GA E N)
    (κ : ℂ) (τs : Finset ℝ) (a : ℝ → ℂ) {f g : GA E N → ℂ} (hf : Continuous f) (hg : Continuous g) :
    E_B P Q κ τs a (f + g) = E_B P Q κ τs a f + E_B P Q κ τs a g := by
  funext m
  simp only [E_B, Pi.add_apply]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have hi : ∀ u : GA E N → ℂ, Continuous u →
      Integrable (fun b => u (P b * Q t m)) (Measure.pi fun _ : ι => boxMeasure E) := fun u hu =>
    integrable_box (hu.comp (hP.mul continuous_const))
  rw [← mul_add, ← integral_add (hi f hf) (hi g hg)]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem E_B_smul {N : ℕ} {Y ι : Type*} [Fintype ι] (P : (ι → Ad E) → GA E N) (Q : ℝ → Y → GA E N)
    (κ : ℂ) (τs : Finset ℝ) (a : ℝ → ℂ) (c : ℂ) (f : GA E N → ℂ) :
    E_B P Q κ τs a (c • f) = c • E_B P Q κ τs a f := by
  funext m
  simp only [E_B, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_const_mul]
  ring

omit [_root_.NumberField.IsTotallyComplex E] in
theorem E_cont_join {n : ℕ} {S : Finset ℕ} (q : ℕ) :
    Continuous fun b : {x : PPos n S // ¬ IsTop q x} → Ad E => (parGL (joinPos (r := q) 0 b) : GA E n) := by
  refine continuous_parGL.comp (continuous_pi fun x => ?_)
  by_cases hx : IsTop q x
  · simp only [joinPos, dif_pos hx]
    exact continuous_const
  · simp only [joinPos, dif_neg hx]
    exact continuous_apply _

theorem E_pos_top {N p q : ℕ} (hpq : p < q) (x : PPos N {p, q}) (hx : ¬ IsTop q x) :
    (x.1.1 : ℕ) < p ∧ p ≤ (x.1.2 : ℕ) ∧ (x.1.2 : ℕ) < q := by
  obtain ⟨s, hs, h1, h2⟩ := x.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  have hx' : ¬ ((x.1.1 : ℕ) < q ∧ q ≤ (x.1.2 : ℕ)) := hx
  rcases hs with rfl | rfl <;> omega

theorem E_pos_bot {N p q : ℕ} (hpq : p < q) (x : PPos N {p, q}) (hx : ¬ IsTop p x) :
    p ≤ (x.1.1 : ℕ) ∧ (x.1.1 : ℕ) < q ∧ q ≤ (x.1.2 : ℕ) := by
  obtain ⟨s, hs, h1, h2⟩ := x.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  have hx' : ¬ ((x.1.1 : ℕ) < p ∧ p ≤ (x.1.2 : ℕ)) := hx
  rcases hs with rfl | rfl <;> omega

theorem E_exp_iff (hD : Dict) {N r : ℕ} (φ : Sm E N) (hφ : IsAutForm φ) (h0 : 0 < r) (h1 : r < N) (c : ℂ) :
    c ∈ Exp r φ.1 ↔ ∃ F ∈ Submodule.span ℂ (Set.range fun t : ℝ => fun g => An.ctn r φ.1 (aT E N r t * g)),
      F ≠ 0 ∧ ∀ (t : ℝ) g, F (aT E N r t * g) = Complex.exp (c * t) * F g := by
  have hd := (hD E N).2.2.2 φ hφ r h0 h1
  constructor
  · rintro ⟨F₀, hct, F, hF, hne, heig⟩
    obtain ⟨κ, -, rfl⟩ := hd.2 F₀ hct
    refine ⟨F, Submodule.span_le.2 ?_ hF, hne, heig⟩
    rintro _ ⟨t, rfl⟩
    have e : (fun g => κ * An.ctn r φ.1 (aT E N r t * g)) = κ • fun g => An.ctn r φ.1 (aT E N r t * g) := rfl
    simp only [e]
    exact Submodule.smul_mem _ κ (Submodule.subset_span ⟨t, rfl⟩)
  · rintro ⟨F, hF, hne, heig⟩
    exact ⟨An.ctn r φ.1, hd.1, F, hF, hne, heig⟩

end PositivityTheory.Rg.Rs.SliceClasses

end
end

section

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.SliceClasses

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem D_chart_left (F : GA E N → ℂ) (h g : GA E N) : chart (fun x => F (h * x)) g = chart F (h * g) := by
  funext x
  simp only [chart, mul_assoc]

def ltS (h : GA E N) : Sm E N →ₗ[ℂ] Sm E N where
  toFun F := ⟨fun g => F.1 (h * g), fun g => by rw [D_chart_left]; exact F.2 (h * g)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem ltS_apply (h : GA E N) (F : Sm E N) (g : GA E N) : (ltS h F).1 g = F.1 (h * g) := rfl

theorem ltS_act (h : GA E N) (o : Op E N) (F : Sm E N) : ltS h (act o F) = act o (ltS h F) := by
  cases o with
  | fin k =>
    refine Subtype.ext (funext fun g => ?_)
    change F.1 (h * g * finGL E N k) = F.1 (h * (g * finGL E N k))
    rw [mul_assoc]
  | cpt k =>
    refine Subtype.ext (funext fun g => ?_)
    change F.1 (h * g * _) = F.1 (h * (g * _))
    rw [mul_assoc]
  | lie X =>
    refine Subtype.ext (funext fun g => ?_)
    change lieD X F.1 (h * g) = lieD X (fun x => F.1 (h * x)) g
    simp only [lieD, D_chart_left]

theorem D_ct_smooth (r : ℕ) (φ : Sm E N) (hl : ∀ γ g, φ.1 (ratGL E N γ * g) = φ.1 g)
    (hlev : IsOpen {k | finRep E N k φ = φ}) :
    ∃ F : Sm E N, F.1 = An.ctn r φ.1 ∧ ∀ X, (lie E N X F).1 = An.ctn r (lie E N X φ).1 := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, hμ, hD, hint⟩ := JDict.exists_normed E N r
  obtain ⟨F, h1, h2⟩ := GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E N r φ hl hlev μ _ hμ hD
  have key : ∀ (f : GA E N → ℂ) g, ∫ x in unipFundamentalDomain E N r, f (unip x * g) ∂μ = An.ctn r f g := by
    intro f g
    rw [hint]
    simp only [An.ctn, constantTerm, GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip]
  exact ⟨F, funext fun g => (h1 g).trans (key _ g), fun X => funext fun g => (h2 X g).trans (key _ g)⟩


open Classical in
def ctSm (r : ℕ) (φ : Sm E N) : Sm E N := if h : An.ctn r φ.1 ∈ Sm E N then ⟨_, h⟩ else 0

theorem ctSm_val (r : ℕ) {φ : Sm E N} (hφ : IsAutForm φ) : (ctSm r φ).1 = An.ctn r φ.1 := by
  obtain ⟨F, hF, -⟩ := D_ct_smooth r φ hφ.left hφ.level
  have h : An.ctn r φ.1 ∈ Sm E N := hF ▸ F.2
  simp only [ctSm, dif_pos h]

theorem ctn_add (r : ℕ) {f g : GA E N → ℂ} (hf : Continuous f) (hg : Continuous g) :
    An.ctn r (f + g) = An.ctn r f + An.ctn r g := by
  funext x
  simp only [An.ctn, Pi.add_apply, constantTerm_add hf hg, mul_add]

theorem ctn_smul (r : ℕ) (c : ℂ) (f : GA E N → ℂ) : An.ctn r (c • f) = c • An.ctn r f := by
  funext x
  simp only [An.ctn, Pi.smul_apply, constantTerm_smul, smul_eq_mul]
  ring

theorem ctSm_act (r : ℕ) {φ : Sm E N} (hφ : IsAutForm φ) (o : Op E N) (hφ' : IsAutForm (act o φ)) :
    ctSm r (act o φ) = act o (ctSm r φ) := by
  obtain ⟨F, hF, hX⟩ := D_ct_smooth r φ hφ.left hφ.level
  have e : ctSm r φ = F := Subtype.ext ((ctSm_val r hφ).trans hF.symm)
  refine Subtype.ext ?_
  rw [ctSm_val r hφ', e]
  cases o with
  | fin k =>
    funext g
    change An.ctn r (fun x => φ.1 (x * finGL E N k)) g = F.1 (g * finGL E N k)
    rw [hF]
    simp only [An.ctn, constantTerm, mul_assoc]
  | cpt k =>
    funext g
    change An.ctn r (fun x => φ.1 (x * _)) g = F.1 (g * _)
    rw [hF]
    simp only [An.ctn, constantTerm, mul_assoc]
  | lie X => exact (hX X).symm

def Aop (N r : ℕ) (τs : Finset ℝ) (a : ℝ → ℂ) : Module.End ℂ (Sm E N) := ∑ t ∈ τs, a t • ltS (aT E N r t)

theorem Aop_apply (r : ℕ) (τs : Finset ℝ) (a : ℝ → ℂ) (F : Sm E N) (g : GA E N) :
    (Aop N r τs a F).1 g = ∑ t ∈ τs, a t * F.1 (aT E N r t * g) := by
  simp only [Aop, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply, ltS_apply, smul_eq_mul]

theorem Aop_act (r : ℕ) (τs : Finset ℝ) (a : ℝ → ℂ) (o : Op E N) (F : Sm E N) :
    Aop N r τs a (act o F) = act o (Aop N r τs a F) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Aop, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, ltS_act]

theorem exists_strictHenselian_absolutely_closed_local_ring (V : Submodule ℂ (Sm E N)) (hV : ∀ φ ∈ V, IsAutForm φ) (r : ℕ) (τs : Finset ℝ) (a : ℝ → ℂ) :
    ∃ T : Sm E N →ₗ[ℂ] Sm E N, ∀ φ ∈ V, T φ = Aop N r τs a (ctSm r φ) := by
  let T₁ : V →ₗ[ℂ] Sm E N :=
    { toFun := fun φ => Aop N r τs a (ctSm r φ.1)
      map_add' := fun φ ψ => by
        have e : ctSm r (φ.1 + ψ.1) = ctSm r φ.1 + ctSm r ψ.1 := by
          refine Subtype.ext ?_
          rw [Submodule.coe_add, ctSm_val r (hV _ (V.add_mem φ.2 ψ.2)), ctSm_val r (hV _ φ.2),
            ctSm_val r (hV _ ψ.2)]
          exact ctn_add r (ContAut.continuous_of_isOpen_stab E N _ (hV _ φ.2).level)
            (ContAut.continuous_of_isOpen_stab E N _ (hV _ ψ.2).level)
        simp only [Submodule.coe_add, e, map_add (f := _)]
      map_smul' := fun c φ => by
        have e : ctSm r (c • φ.1) = c • ctSm r φ.1 := by
          refine Subtype.ext ?_
          rw [Submodule.coe_smul, ctSm_val r (hV _ (V.smul_mem c φ.2)), ctSm_val r (hV _ φ.2)]
          exact ctn_smul r c _
        simp only [Submodule.coe_smul, e, map_smul, RingHom.id_apply] }
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T₁
  exact ⟨T, fun φ hφ => LinearMap.congr_fun hT ⟨φ, hφ⟩⟩

end PositivityTheory.Rg.Rs.SliceClasses

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

namespace E

theorem cpt_mem {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {F : Sm E (r + s)} (hF : F ∈ indSub U₁ U₂)
    (k : Kinf E (r + s)) : cptRep E (r + s) k F ∈ indSub U₁ U₂ := by
  have e : (cptRep E (r + s) k F).1 = fun x => F.1 (x * cf (r + s) k 1) := by
    funext x
    simp only [cf, map_one, mul_one]
    rfl
  change IsInd U₁ U₂ (cptRep E (r + s) k F).1
  rw [e]
  exact isInd_rt hF k 1

end E

theorem exists_expansion {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {F : Sm E (r + s)}
    (hF : F ∈ indSub U₁ U₂) (hK : F ∈ finVec (cptRep E (r + s))) :
    ∃ (n : ℕ) (G : Fin n → GA E r × GA E s → ℂ) (C : Fin n → Lie E (r + s) → ℂ)
      (b₁ : Lie E (r + s) → GL (Fin r) (Cinf E)) (b₂ : Lie E (r + s) → GL (Fin s) (Cinf E)),
      (∀ j, G j ∈ tens2 U₁ U₂) ∧ (∀ j, ContDiffAt ℝ ∞ (C j) (oneL E (r + s))) ∧
      ContDiffAt ℝ ∞ (fun y => toL (b₁ y).val) (oneL E (r + s)) ∧
      ContDiffAt ℝ ∞ (fun y => toL (b₂ y).val) (oneL E (r + s)) ∧
      b₁ (oneL E (r + s)) = 1 ∧ b₂ (oneL E (r + s)) = 1 ∧
      ∀ {f₁ : Sm E r →ₗ[ℂ] Sm E r} {f₂ : Sm E s →ₗ[ℂ] Sm E s}, Good U₁ U₂ f₁ f₂ → ∀ m : GA E r × GA E s,
        chart (ind f₁ f₂ F.1) (lev (Ad E) r s m) =ᶠ[nhds (oneL E (r + s))]
          fun y => ∑ j, C j y * tensOp f₁ f₂ (G j) (m.1 * infGL E r (b₁ y), m.2 * infGL E s (b₂ y)) := by
  obtain ⟨b₁, b₂, κ, u, hb₁, hb₂, hκ, hb₁1, hb₂1, hκ1, hloc⟩ := exists_local E r s
  obtain ⟨n, ψ, C, hψ, hC, e⟩ := GlobalTheory.KFinExp.exists_expansion E (r + s) F hK
  have hψ' : ∀ j, ψ j ∈ indSub U₁ U₂ := fun j => Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact PositivityTheory.Rg.Rs.InducedTensorMap.E.cpt_mem hF k) (hψ j)
  have hκ1' : toL (κ (oneL E (r + s))).1 = oneL E (r + s) := by rw [hκ1]; rfl
  refine ⟨n, fun j => res 1 (ψ j).1, fun j y => C j (toL (κ y).1), b₁, b₂, fun j => ?_, fun j => ?_, hb₁, hb₂, hb₁1,
    hb₂1, ?_⟩
  · have := (hψ' j).2 1 1
    rwa [cf_one] at this
  · exact ContDiffAt.comp (oneL E (r + s)) (by rw [hκ1']; exact hC j) hκ
  intro f₁ f₂ H m
  filter_upwards [hloc] with y hy
  have hyw : y = toL (unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y) * Unitary.toUnits (κ y)).val := by
    show y = toL ((unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y)).val * (κ y).1)
    rw [← hy]
    rfl
  conv_lhs => rw [hyw, chart_val]
  obtain ⟨v, hv⟩ := lev_mul_infGL m (u y) (b₁ y) (b₂ y) (κ y)
  rw [hv, ind_apply H (show IsInd U₁ U₂ F.1 from hF) v _ (κ y) 1]
  have er : res (cf (r + s) (κ y) 1) F.1 = ∑ j, C j (toL (κ y).1) • res 1 (ψ j).1 := by
    have h1 : res (cf (r + s) (κ y) 1) F.1 = res 1 (cptRep E (r + s) (κ y) F).1 := by
      funext z
      simp only [res_apply, cf, map_one, mul_one]
      rfl
    rw [h1, e]

    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  rw [er]

  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem ind_mem_Sm {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : Sm E (r + s)} (hF : F ∈ indSub U₁ U₂)
    (hK : F ∈ finVec (cptRep E (r + s))) : ind f₁ f₂ F.1 ∈ Sm E (r + s) := by
  have key : ∀ {F : Sm E (r + s)}, F ∈ indSub U₁ U₂ → F ∈ finVec (cptRep E (r + s)) → ∀ m,
      ContDiffAt ℝ ∞ (chart (ind f₁ f₂ F.1) (lev (Ad E) r s m)) (oneL E (r + s)) := fun hF hK m => by
    obtain ⟨n, G, C, b₁, b₂, hG, hC, hb₁, hb₂, -, -, e⟩ := exists_expansion hF hK
    exact ContDiffAt.congr_of_eventuallyEq (ContDiffAt.sum fun j _ =>
      (hC j).mul (contDiffAt_tens b₁ b₂ hb₁ hb₂ (tensOp_mem f₁ f₂ (hG j)) m)) (e H m)
  refine GlobalTheory.DiscSMO.mem_Sm_of_one fun x => ?_
  obtain ⟨u, m, k, g, rfl⟩ := exists_decomp x
  have e1 : chart (ind f₁ f₂ F.1) (unip u * lev (Ad E) r s m * cf (r + s) k g) =
      chart (ind f₁ f₂ F.1) (lev (Ad E) r s m * cf (r + s) k g) := by
    funext z
    unfold chart
    split_ifs
    · simp only [mul_assoc]
      exact ind_left H hF u _
    · rfl
  rw [e1, cf, infGL_comm, ← mul_assoc]
  refine GlobalTheory.DiscSMO.contDiffAt_chart_mul ?_
  rw [← chart_rt_fin]
  have e2 : (fun x => (fun x => ind f₁ f₂ F.1 (x * infGL E (r + s) (Unitary.toUnits k))) (x * finGL E (r + s) g)) =
      ind f₁ f₂ (rt E (r + s) (cf (r + s) k g) F).1 := by
    funext z
    rw [show (rt E (r + s) (cf (r + s) k g) F).1 = fun y => F.1 (y * cf (r + s) k g) from rfl,
      ind_rt H hF k g z, cf, infGL_comm]
    exact congrArg _ (mul_assoc _ _ _)
  rw [e2]
  exact key (isInd_rt hF k g) (finVec_rt hK k g) m

end PositivityTheory.Rg.Rs.InducedTensorMap

end
end
