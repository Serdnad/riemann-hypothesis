module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.LatSOfMem
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlobApprox
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle002
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LocalToGlobal.HermitianForms.PrkSmul
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle001
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG

namespace Formalism.L2.GlobalTheoryTheory.Br

section Proof

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

omit [Field E] [NumberField E] [Algebra F E] in
theorem finiteAdeleRing_nontrivial : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)⟩
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h' := congrArg (evalV F v) h
  rw [map_zero, map_one] at h'
  exact zero_ne_one h'

theorem latS_mono_fin {Λ Λ' : Submodule (𝓞 E) (Fin n → E)} (h : Λ ≤ Λ') :
    latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ ≤ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ' :=
  Submodule.span_mono (Set.image_mono h)

theorem latS_functional (Λ : Submodule (𝓞 E) (Fin n → E)) (f : Module.Dual E (Fin n → E))
    (hf : ∀ y ∈ Λ, f y = 0) (x : Fin n → E)
    (hx : (fun i => ι (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ) : f x = 0 := by
  set c : Fin n → E := fun i => f (Pi.single i 1)
  have hfc : ∀ y : Fin n → E, f y = ∑ i, c i * y i := by
    intro y
    have hy : y = ∑ i, y i • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hy]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have key : ∀ u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ, ∑ i, ι (c i) * u i = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨y, hy, rfl⟩ := hu

      simp only [← map_mul, ← map_sum]
      rw [← hfc, hf y hy, map_zero]
    | zero => simp
    | add u w _ _ hu hw =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [hu, hw, add_zero]
    | smul a u _ hu =>
      have h : ∑ i, ι (c i) * (a • u) i = (a : 𝒜) * ∑ i, ι (c i) * u i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.smul_apply]
        show _ * ((a : 𝒜) * u i) = _
        ring
      rw [h, hu, mul_zero]
  have h1 := key _ hx

  simp only [← map_mul, ← map_sum] at h1
  rw [← hfc] at h1
  exact inclE_injective_fin h1
where
  inclE_injective_fin {a : E} (h : ι a = 0) : a = 0 :=
    have := finiteAdeleRing_nontrivial (F := F)
    Formalism.UG.P.inclE_injective F E (FiniteAdeleRing (𝓞 F) F) (by rw [h, map_zero])

theorem latS_mem_span (Λ : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (hx : (fun i => ι (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ) :
    x ∈ Submodule.span E (Λ : Set (Fin n → E)) := by
  by_contra hxV
  obtain ⟨f, hfx, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxV inferInstance
  refine hfx (latS_functional (F := F) Λ f (fun y hy => ?_) x hx)
  have h2 : f y ∈ (Submodule.span E (Λ : Set (Fin n → E))).map f :=
    Submodule.mem_map_of_mem (Submodule.subset_span hy)
  rw [hf] at h2
  exact (Submodule.mem_bot E).1 h2

theorem latLocGlob_main (Λ : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (x : Fin n → E)
    (hx : (fun i => ι (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ) : x ∈ Λ := by
  have hxV := latS_mem_span (F := F) Λ x hx
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Submodule.span E (Λ : Set (Fin n → E)))
  let b := Module.finBasis E C
  let W : Submodule (𝓞 E) (Fin n → E) :=
    Submodule.span (𝓞 E) (Set.range fun i => (b i : Fin n → E))
  let Λ' : Submodule (𝓞 E) (Fin n → E) := Λ ⊔ W
  have hfin' : Module.Finite (𝓞 E) Λ' :=
    Module.Finite.iff_fg.mpr ((Module.Finite.iff_fg.mp hfin).sup (Submodule.fg_span (Set.finite_range _)))
  have hV' : Submodule.span E (Λ : Set (Fin n → E)) ≤ Submodule.span E (Λ' : Set (Fin n → E)) :=
    Submodule.span_mono (fun y hy => Submodule.mem_sup_left hy)
  have hC' : C ≤ Submodule.span E (Λ' : Set (Fin n → E)) := by
    intro c hc
    have h := congrArg Subtype.val (b.sum_repr ⟨c, hc⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
    rw [← h]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)
  have hspan' : Submodule.span E (Λ' : Set (Fin n → E)) = ⊤ := by
    rw [eq_top_iff, ← hC.sup_eq_top]
    exact sup_le hV' hC'
  have hx' : x ∈ Λ' := by
    have h := Formalism.UG.P.csGlob_one (F := F) Formalism.UG.P.csGlob_intAdApprox Λ' hfin' hspan'
    rw [← h]
    show ((1⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) *ᵥ (fun i => ι (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ'
    rw [inv_one, Units.val_one, one_mulVec]
    exact latS_mono_fin le_sup_left hx
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
  have hwC : w ∈ C :=
    (Submodule.span_le (p := C.restrictScalars (𝓞 E))).2 (by rintro _ ⟨i, rfl⟩; exact (b i).2) hw
  have hwV : w ∈ Submodule.span E (Λ : Set (Fin n → E)) := by
    have e : w = (y + w) - y := by abel
    rw [e]
    exact sub_mem hxV (Submodule.subset_span hy)
  have hw0 : w = 0 := Submodule.disjoint_def.1 hC.disjoint w hwV hwC
  rw [hw0, add_zero]
  exact hy

end Proof

theorem latLocGlob : LatLocGlob := by
  intro F E _ _ _ _ _ n Λ hfin x hx
  exact latLocGlob_main Λ hfin x hx

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open NumberField Formalism.UG Matrix

variable {E : Type} [Field E] [NumberField E]

theorem sig_natInv (σ : E →+* E) (T : ℕ) : σ ((T : E)⁻¹) = (T : E)⁻¹ := by
  simp [map_inv₀, map_natCast]

theorem galois_image_integers (σ : E →+* E) (r : 𝓞 E) : σ (r : E) ∈ (algebraMap (𝓞 E) E).range :=
  ⟨⟨σ (r : E), (r.2).map σ.toIntAlgHom⟩, rfl⟩

theorem fix_orthogonal_vector {N N' : ℕ} (σ : E →+* E) (hσ : ∀ (φ : E →+* ℂ) (x : E), φ (σ x) = (starRingEnd ℂ) (φ x))
    (J : Matrix (Fin N) (Fin N) E) (J' : Matrix (Fin N') (Fin N') E)
    (hdef : ∀ (φ : E →+* ℂ) (x : Fin N → E), ∃ r : ℝ, 0 ≤ r ∧ φ (hform σ J x x) = r ∧ (r = 0 → x = 0))
    (ι : (Fin N' → E) →ₗ[E] (Fin N → E)) (z0 : Fin N → E)
    (hiso : ∀ x x', hform σ J (ι x) (ι x') = hform σ J' x x')
    (horth : ∀ x, hform σ J (ι x) z0 = 0 ∧ hform σ J z0 (ι x) = 0)
    (hspan : ∀ y, ∃ (x : Fin N' → E) (s : E), y = ι x + s • z0)
    (T : ℕ) (hTp : T.Prime) (hdeg : Module.finrank ℚ E < T - 1) (hzz : hform σ J z0 z0 = T)
    (L1 L2 : Submodule (𝓞 E) (Fin N' → E))
    (hsd2 : (∀ y, (∀ x ∈ L2, hform σ J' x y ∈ (algebraMap (𝓞 E) E).range) → y ∈ L2) ∧
      ∀ x ∈ L2, ∀ y ∈ L2, hform σ J' x y ∈ (algebraMap (𝓞 E) E).range)
    (γ : Matrix (Fin N) (Fin N) E) (hγ : ∀ x y, hform σ J (γ *ᵥ x) (γ *ᵥ y) = hform σ J x y)
    (hlat : Formalism.L2.Forms.mulLat γ (L1.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0}) =
      L2.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0})
    (P : Ideal (𝓞 E)) (hP : P.IsPrime) (hTP : (T : 𝓞 E) ∈ P)
    (hres : ∀ y : Fin N → E, (∀ w ∈ L1.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0},
        hform σ J w y ∈ (algebraMap (𝓞 E) E).range) →
      ∀ r r' : 𝓞 E, (r : E) = hform σ J z0 y → (r' : E) = hform σ J z0 (γ *ᵥ y) → r - r' ∈ P) :
    γ *ᵥ z0 = z0 := by
  have hT1 : 1 < T := hTp.one_lt
  have hT0 : (T : E) ≠ 0 := by exact_mod_cast hTp.ne_zero
  set z' : Fin N → E := (T : E)⁻¹ • z0 with hz'
  have hz0 : z0 = (T : E) • z' := by rw [hz', smul_smul, mul_inv_cancel₀ hT0, one_smul]

  have hzz' : (T : E) * hform σ J z' z' = 1 := by
    rw [hz', hform_smul_left, hform_smul_right, hzz, sig_natInv]; field_simp
  have hz0z' : hform σ J z0 z' = 1 := by
    rw [hz', hform_smul_right, hzz]; field_simp

  have memL : ∀ (L : Submodule (𝓞 E) (Fin N' → E)) w, w ∈ L.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0} →
      ∃ l ∈ L, ∃ r : 𝓞 E, w = ι l + (r : E) • z0 := by
    intro L w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
    obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.1 ha
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hb
    exact ⟨l, hl, r, by rw [← algebraMap_smul E r z0]; rfl⟩

  have hd1 : ∀ w ∈ L1.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0},
      hform σ J w z' ∈ (algebraMap (𝓞 E) E).range := by
    intro w hw
    obtain ⟨l, _, r, rfl⟩ := memL L1 w hw
    rw [hform_add_left, hform_smul_left, hz', hform_smul_right, hform_smul_right, (horth l).1, hzz]
    have : (T : E)⁻¹ * 0 + σ (r : E) * ((T : E)⁻¹ * (T : E)) = σ (r : E) := by
      rw [mul_zero, zero_add, inv_mul_cancel₀ hT0, mul_one]
    rw [this]; exact galois_image_integers σ r

  have hd2 : ∀ w ∈ L2.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0},
      hform σ J w (γ *ᵥ z') ∈ (algebraMap (𝓞 E) E).range := by
    intro w hw
    rw [← hlat] at hw
    obtain ⟨w1, hw1, rfl⟩ := Submodule.mem_map.1 hw
    show hform σ J (γ *ᵥ w1) (γ *ᵥ z') ∈ _
    rw [hγ]; exact hd1 w1 hw1

  obtain ⟨y1, s, hys⟩ := hspan (γ *ᵥ z')
  have hy1 : y1 ∈ L2 := by
    apply hsd2.1
    intro x hx
    have hmem : ι x ∈ L2.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0} :=
      Submodule.mem_sup_left (Submodule.mem_map.2 ⟨x, hx, rfl⟩)
    have := hd2 _ hmem
    rwa [hys, hform_add_right, hform_smul_right, (horth x).1, mul_zero, add_zero, hiso] at this
  obtain ⟨t, ht⟩ : ∃ t : 𝓞 E, (t : E) = s * T := by
    have hmem : z0 ∈ L2.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0} :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self z0)
    have := hd2 _ hmem
    rw [hys, hform_add_right, hform_smul_right, (horth y1).2, hzz, zero_add] at this
    obtain ⟨t, ht⟩ := this
    exact ⟨t, ht⟩
  have hyt : γ *ᵥ z' = ι y1 + (t : E) • z' := by
    rw [hys, ht, hz0, smul_smul]

  have hγzz : (T : E) * hform σ J (γ *ᵥ z') (γ *ᵥ z') = 1 := by rw [hγ]; exact hzz'
  have hmemy : γ *ᵥ z' ∈ L2.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z'} := by
    rw [hyt]
    refine Submodule.add_mem_sup (Submodule.mem_map.2 ⟨y1, hy1, rfl⟩) ?_
    have h := Submodule.smul_mem (Submodule.span (𝓞 E) {z'}) t (Submodule.mem_span_singleton_self z')
    rw [← algebraMap_smul E t z'] at h
    exact h
  have hint : ∀ x ∈ L2.map (ι.restrictScalars (𝓞 E)), ∃ a : 𝓞 E, (a : E) = hform σ J x x := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨a, ha⟩ := hsd2.2 l hl l hl
    refine ⟨a, ?_⟩
    show (a : E) = hform σ J (ι l) (ι l)
    rw [hiso]; exact ha
  have hzL : ∀ x ∈ L2.map (ι.restrictScalars (𝓞 E)), hform σ J x z' = 0 ∧ hform σ J z' x = 0 := by
    intro x hx
    obtain ⟨l, _, rfl⟩ := Submodule.mem_map.1 hx
    refine ⟨?_, ?_⟩
    · show hform σ J (ι l) z' = 0
      rw [hz', hform_smul_right, (horth l).1, mul_zero]
    · show hform σ J z' (ι l) = 0
      rw [hz', hform_smul_left, (horth l).2, mul_zero]
  obtain ⟨b, ⟨k, hk, hbk⟩, hb⟩ :=
    length_inverse_bound σ hσ J hdef (L2.map (ι.restrictScalars (𝓞 E))) hint z' hzL T hT1 hzz' (γ *ᵥ z') hmemy hγzz

  have hbP : b - 1 ∈ P := by
    have h1 := hres z' hd1 1 b (by rw [hz0z']; simp) (by rw [hb, hform_smul_right, hz0z', mul_one])
    have : b - 1 = -(1 - b) := by ring
    rw [this]; exact P.neg_mem h1
  have hb1 : b = 1 := root_eq_one P T k b hTp hP hTP hk hbk hbP hdeg
  rw [hb1] at hb
  have : γ *ᵥ z' = z' := by rw [hb]; simp
  rw [hz0, Matrix.mulVec_smul, this]

theorem fix_restrict {N N' : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (J' : Matrix (Fin N') (Fin N') E)
    (ι : (Fin N' → E) →ₗ[E] (Fin N → E)) (hinj : Function.Injective ι) (z0 : Fin N → E)
    (hiso : ∀ x x', hform σ J (ι x) (ι x') = hform σ J' x x')
    (horth : ∀ x, hform σ J (ι x) z0 = 0 ∧ hform σ J z0 (ι x) = 0)
    (hspan : ∀ y, ∃ (x : Fin N' → E) (s : E), y = ι x + s • z0)
    (hzz : hform σ J z0 z0 ≠ 0)
    (γ : Matrix (Fin N) (Fin N) E) (hγ : ∀ x y, hform σ J (γ *ᵥ x) (γ *ᵥ y) = hform σ J x y) (hfix : γ *ᵥ z0 = z0) :
    ∃ δ : Matrix (Fin N') (Fin N') E, (∀ x, γ *ᵥ ι x = ι (δ *ᵥ x)) ∧
      ∀ x y, hform σ J' (δ *ᵥ x) (δ *ᵥ y) = hform σ J' x y := by
  have hrange : ∀ x, γ *ᵥ ι x ∈ LinearMap.range ι := by
    intro x
    obtain ⟨x', s, hs⟩ := hspan (γ *ᵥ ι x)
    have h0 : hform σ J (γ *ᵥ ι x) z0 = 0 := by
      conv_lhs => rw [← hfix]
      rw [hγ]; exact (horth x).1
    rw [hs, hform_add_left, hform_smul_left, (horth x').1, zero_add] at h0
    have hs0 : σ s = 0 := (mul_eq_zero.1 h0).resolve_right hzz
    have : s = 0 := (map_eq_zero σ).1 hs0
    rw [hs, this, zero_smul, add_zero]; exact ⟨x', rfl⟩
  let e := LinearEquiv.ofInjective ι hinj
  let g : (Fin N' → E) →ₗ[E] LinearMap.range ι :=
    LinearMap.codRestrict (LinearMap.range ι) ((Matrix.mulVecLin γ).comp ι) hrange
  let f : (Fin N' → E) →ₗ[E] (Fin N' → E) := e.symm.toLinearMap.comp g
  have hf : ∀ x, ι (f x) = γ *ᵥ ι x := by
    intro x
    have h1 : (e (f x) : Fin N → E) = ι (f x) := rfl
    rw [← h1]
    show ((e (e.symm (g x)) : LinearMap.range ι) : Fin N → E) = _
    rw [LinearEquiv.apply_symm_apply]; rfl
  refine ⟨LinearMap.toMatrix' f, fun x => ?_, fun x y => ?_⟩
  · rw [LinearMap.toMatrix'_mulVec, hf]
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, ← hiso, hf, hf, hγ, hiso]

end Formalism.L2.GlobalTheoryTheory.Br
end
end
