module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.IsDualPair
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Mathlib.NumberTheory.Padics.RingHoms
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle002
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
import Mathlib.RingTheory.PowerSeries.Inverse
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
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.Algebra.Algebra.ZMod
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem lc_of_open {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup M] [Module R M] (ρ : Representation R Γ M) (H : Subgroup Γ) (hH : IsOpen (H : Set Γ))
    (h : ∀ m, IsLocallyConstant fun g : H => ρ g m) : LC ρ := by
  intro m
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hU : IsOpen ((Subtype.val : H → Γ) '' {z : H | ρ z m = m}) :=
    hH.isOpenMap_subtype_val _ ((h m).isOpen_fiber m)
  have h1 : (1 : Γ) ∈ (Subtype.val : H → Γ) '' {z : H | ρ z m = m} := ⟨1, by simp, rfl⟩
  have ht : Filter.Tendsto (fun y => x⁻¹ * y) (nhds x) (nhds 1) := by
    have h0 := (continuous_const_mul x⁻¹).tendsto x
    simpa using h0
  filter_upwards [ht (hU.mem_nhds h1)] with y hy
  obtain ⟨z, hz, hzy⟩ := hy
  have hz' : ρ z m = m := hz
  have hy : y = x * z := by rw [hzy]; group
  rw [hy, map_mul]
  show ρ x (ρ z m) = ρ x m
  rw [hz']

private theorem lc_mat {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hev : ∀ᶠ y in nhds x, ∀ i j, f y i j = f x i j := by
    simp only [Filter.eventually_all]
    intro i j
    exact (h i j).eventually_eq x
  filter_upwards [hev] with y hy
  exact Matrix.ext hy

private theorem lc_padic {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (f : ℤ_[l] →+* R) (hl : (l : R) = 0) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hev : ∀ᶠ y in nhds x, ‖y - x‖ < 1 := by
    filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
    simpa [dist_eq_norm] using hy
  filter_upwards [hev] with y hy
  obtain ⟨z, hz⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 hy
  have hyz : y = x + (l : ℤ_[l]) * z := by rw [← hz]; ring
  rw [hyz, map_add (f := _), map_mul, map_natCast, hl, zero_mul, add_zero]

private theorem maximalIdeal_powerSeries_eq_span_X (K : Type) [Field K] :
    IsLocalRing.maximalIdeal (PowerSeries K) = Ideal.span {(PowerSeries.X : PowerSeries K)} := by
  ext φ
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff,
    PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]

private theorem isLocallyConstant_pi_of_forall_isLocallyConstant {Γ ι Y : Type} [TopologicalSpace Γ] [Finite ι] (f : Γ → ι → Y)
    (h : ∀ i, IsLocallyConstant fun g => f g i) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hev : ∀ᶠ y in nhds x, ∀ i, f y i = f x i :=
    Filter.eventually_all.2 fun i => (h i).eventually_eq x
  filter_upwards [hev] with y hy
  exact funext hy

private theorem isLocallyConstant_comp_of_adicCont_of_pow_eq_zero {Γ A B : Type} [TopologicalSpace Γ] [CommRing A] [CommRing B] (s : A) (N : ℕ)
    (φ : A →+* B) (hs : φ s ^ N = 0) (f : Γ → A) (hf : AdicCont (Ideal.span {s}) f) :
    IsLocallyConstant fun g => φ (f g) := by
  have hI : ∀ a ∈ Ideal.span {s} ^ N, φ a = 0 := by
    intro a ha
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, map_pow, hs, mul_zero]
  have h2 := (hf N).comp (Ideal.Quotient.lift (Ideal.span {s} ^ N) φ hI)
  convert h2 using 1
  funext g
  exact (Ideal.Quotient.lift_mk (Ideal.span {s} ^ N) φ hI).symm

theorem UpperTheory.V.Pa.lc1 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (m : ℕ), (IsLocallyConstant fun g : G.G₀ => k.ρ1 (x.Am m) (h.p₀ g)) ∧ (IsLocallyConstant fun g : G.Γ => epsD k (x.Am m) (h.p g)) ∧ ∀ (χ : G.Γ → DD (x.Am m) k.g) (V : Submodule x.A (Matrix (Fin n) (Fin n) (DD (x.Am m) k.g))) (rep : Representation x.A G.Γ V), IsLocallyConstant χ → IsAd G.frame (fun g => k.ρ1 (x.Am m) (h.p₀ g)) χ V rep → LC rep := by
  intro l _ L G G0 h n x k m
  obtain ⟨-, -, -, -, hlD, htA, htD, -, -⟩ := finAm l G0.frame n x m k.g
  have hM : IsLocalRing.maximalIdeal (PowerSeries x.K) = Ideal.span {x.t} := maximalIdeal_powerSeries_eq_span_X x.K
  have hp0 : Continuous h.p₀ := continuous_induced_rng.2 (h.cont.comp continuous_subtype_val)
  have hE : IsLocallyConstant fun g : G0.G₀ =>
      DD.epM (fun j => (k.κ j g).map (algebraMap x.A (x.Am m))) := by
    apply lc_mat
    intro a b
    have hv : IsLocallyConstant fun g : G0.G₀ => fun j => algebraMap x.A (x.Am m) (k.κ j g a b) := by
      apply isLocallyConstant_pi_of_forall_isLocallyConstant
      intro j
      exact isLocallyConstant_comp_of_adicCont_of_pow_eq_zero (algebraMap x.A x.A x.t) m (algebraMap x.A (x.Am m)) (by simpa using htA) _
        ((k.mem j).2.1 a b)
    exact hv.comp (fun v => ({ a := 0, ep := v, ep' := 0, eta := 0 } : DD (x.Am m) k.g))
  have hR : IsLocallyConstant fun g : G0.G₀ => x.ρX (DD (x.Am m) k.g) g := by
    apply lc_mat
    intro a b
    simp only [NP.ρX, Matrix.map_apply]
    exact isLocallyConstant_comp_of_adicCont_of_pow_eq_zero x.t m (algebraMap x.A (DD (x.Am m) k.g)) htD _ (by rw [← hM]; exact x.cont a b)
  have hρ : IsLocallyConstant fun g : G0.G₀ => k.ρ1 (x.Am m) g :=
    (hE.comp (fun M => 1 + M)).comp₂ hR (· * ·)
  have hρ' : IsLocallyConstant fun g : G.G₀ => k.ρ1 (x.Am m) (h.p₀ g) := hρ.comp_continuous hp0
  refine ⟨hρ', ?_, ?_⟩
  · have hl' : ((l : ℕ) : DD (x.Am m) k.g) = 0 := by simpa using hlD 1
    exact (lc_padic ((algebraMap x.A (DD (x.Am m) k.g)).comp (algebraMap ℤ_[l] x.A)) hl').comp_continuous
      (Units.continuous_val.comp (G0.ε_cont.comp h.cont))
  · intro χ V rep hχ hAd
    apply lc_of_open rep G.η.ker G.η_open
    intro Z
    have hinv : IsLocallyConstant fun g : G.G₀ => k.ρ1 (x.Am m) (h.p₀ g⁻¹) :=
      hρ'.comp_continuous continuous_inv
    have hχ' : IsLocallyConstant fun g : G.G₀ => χ g := hχ.comp_continuous continuous_subtype_val
    have key : IsLocallyConstant fun g : G.G₀ => ((rep g Z : V) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) := by
      have e : (fun g : G.G₀ => ((rep g Z : V) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g))) =
          fun g : G.G₀ => χ g • (k.ρ1 (x.Am m) (h.p₀ g) * (Z : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) *
            k.ρ1 (x.Am m) (h.p₀ g⁻¹)) := by
        funext g
        exact hAd.1 g Z
      rw [e]
      exact hχ'.comp₂ (hρ'.comp₂ hinv fun A B => A * (Z : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) * B)
        fun c M => c • M
    exact (IsLocallyConstant.iff_eventually_eq _).2 fun g =>
      (key.eventually_eq g).mono fun y hy => Subtype.ext hy
end

section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section Gen

variable {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n a : ℕ}

private theorem mem_blkMat_iff_mem_of_same_block_and_mem_off {V₁ V₂ : Submodule A R} {Z : Matrix (Fin n) (Fin n) R} :
    Z ∈ blkMat n a V₁ V₂ ↔ ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j ∈ V₁) ∧
      (¬((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j ∈ V₂) :=
  Iff.rfl

private theorem blk_tr {V₁ V₂ : Submodule A R} {Z : Matrix (Fin n) (Fin n) R} (hZ : Z ∈ blkMat n a V₁ V₂) :
    Zᵀ ∈ blkMat n a V₁ V₂ := by
  rw [mem_blkMat_iff_mem_of_same_block_and_mem_off] at hZ ⊢
  intro i j
  obtain ⟨h1, h2⟩ := hZ j i
  exact ⟨fun h => h1 h.symm, fun h => h2 (fun h' => h h'.symm)⟩

private def Act (U₁ U₂ V₁ V₂ : Submodule A R) : Prop :=
  (∀ u ∈ U₁, ∀ v ∈ V₁, u * v ∈ V₁) ∧ (∀ u ∈ U₁, ∀ v ∈ V₂, u * v ∈ V₂) ∧
    (∀ u ∈ U₂, ∀ v ∈ V₁, u * v ∈ V₂) ∧ (∀ u ∈ U₂, ∀ v ∈ V₂, u * v ∈ V₁)

private theorem blk_mul {U₁ U₂ V₁ V₂ : Submodule A R} (H : Act U₁ U₂ V₁ V₂) {P Z : Matrix (Fin n) (Fin n) R}
    (hP : P ∈ blkMat n a U₁ U₂) (hZ : Z ∈ blkMat n a V₁ V₂) : P * Z ∈ blkMat n a V₁ V₂ := by
  rw [mem_blkMat_iff_mem_of_same_block_and_mem_off] at hP hZ ⊢
  obtain ⟨h11, h12, h21, h22⟩ := H
  intro i j
  constructor
  · intro hij
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ (fun k _ => ?_)
    by_cases hik : ((i : ℕ) < a ↔ (k : ℕ) < a)
    · exact h11 _ ((hP i k).1 hik) _ ((hZ k j).1 (hik.symm.trans hij))
    · have hkj : ¬((k : ℕ) < a ↔ (j : ℕ) < a) := fun h => hik (hij.trans h.symm)
      exact h22 _ ((hP i k).2 hik) _ ((hZ k j).2 hkj)
  · intro hij
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ (fun k _ => ?_)
    by_cases hik : ((i : ℕ) < a ↔ (k : ℕ) < a)
    · have hkj : ¬((k : ℕ) < a ↔ (j : ℕ) < a) := fun h => hij (hik.trans h)
      exact h12 _ ((hP i k).1 hik) _ ((hZ k j).2 hkj)
    · have hkj : ((k : ℕ) < a ↔ (j : ℕ) < a) := by tauto
      exact h21 _ ((hP i k).2 hik) _ ((hZ k j).1 hkj)

private theorem blk_sand {U₁ U₂ V₁ V₂ : Submodule A R} (H : Act U₁ U₂ V₁ V₂) {P Q Z : Matrix (Fin n) (Fin n) R}
    (hP : P ∈ blkMat n a U₁ U₂) (hQ : Q ∈ blkMat n a U₁ U₂) (hZ : Z ∈ blkMat n a V₁ V₂) :
    P * Z * Q ∈ blkMat n a V₁ V₂ := by
  have h1 := blk_mul H hP hZ
  have h2 := blk_tr (blk_mul H (blk_tr hQ) (blk_tr h1))
  simpa [Matrix.transpose_mul] using h2

private theorem alg_smul_mem {V : Submodule A (Matrix (Fin n) (Fin n) R)} (c : A) {Z : Matrix (Fin n) (Fin n) R}
    (hZ : Z ∈ V) : algebraMap A R c • Z ∈ V := by
  rw [algebraMap_smul]
  exact V.smul_mem c hZ

end Gen

section Parts

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g : ℕ}

private theorem ep_algebraMap_eq_zero (c : A) (j : Fin g) : (algebraMap A (DD X g) c).ep j = 0 := rfl

private theorem ep'_algebraMap_eq_zero (c : A) (j : Fin g) : (algebraMap A (DD X g) c).ep' j = 0 := rfl

private theorem eta_algebraMap_eq_zero (c : A) : (algebraMap A (DD X g) c).eta = 0 := rfl

private theorem mem_part {p q r s : Bool} {y : DD X g} : y ∈ ddPart A X g p q r s ↔
    (p = false → y.a = 0) ∧ (q = false → ∀ j, y.ep j = 0) ∧ (r = false → ∀ j, y.ep' j = 0) ∧ (s = false → y.eta = 0) := by
  show ((p = false → y.a = 0) ∧ (q = false → y.ep = 0) ∧ (r = false → y.ep' = 0) ∧ (s = false → y.eta = 0)) ↔ _
  simp only [funext_iff, Pi.zero_apply]

private theorem act1 : Act (ddPart A X g true false false false) (ddPart A X g false true false false)
    (ddPart A X g true false false false) (ddPart A X g false true false false) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro u hu v hv <;> rw [mem_part] at hu hv ⊢ <;> simp_all

private theorem act1s : Act (ddPart A X g true false false false) (ddPart A X g false true false false)
    (ddPart A X g false false false true) (ddPart A X g false false true false) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro u hu v hv <;> rw [mem_part] at hu hv ⊢ <;> simp_all

private theorem act2 : Act (ddPart A X g true false false false) (ddPart A X g false true false false)
    (ddPart A X g false false true false) (ddPart A X g false false false true) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro u hu v hv <;> rw [mem_part] at hu hv ⊢ <;> simp_all

end Parts

private theorem galois_lift_mem_first_order_deformations {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type)
    [CommRing X] [Algebra x.A X] (g : F.G₀) : k.ρ1 X g ∈ W1 n x.A X k.g x.a := by
  have hP : (1 + DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) ∈ W1 n x.A X k.g x.a := by
    show _ ∈ blkMat n x.a (ddPart x.A X k.g true false false false) (ddPart x.A X k.g false true false false)
    refine mem_blkMat_iff_mem_of_same_block_and_mem_off.2 (fun i j => ⟨fun h => ?_, fun h => ?_⟩)
    · have hκ : ∀ m, k.κ m g i j = 0 := fun m => by
        have hm := ((mem_blkMat_iff_mem_of_same_block_and_mem_off.1 ((k.mem m).1 g)) i j).1 h
        simpa using hm
      rw [mem_part]
      by_cases hij : i = j
      · subst hij
        simp [Matrix.one_apply, DD.epM, hκ]
      · simp [hij, Matrix.one_apply, DD.epM, hκ]
    · have hne : i ≠ j := by
        rintro rfl
        exact h Iff.rfl
      rw [mem_part]
      simp [hne, Matrix.one_apply, DD.epM]
  have hZ : x.ρX (DD X k.g) g ∈ W1 n x.A X k.g x.a := by
    show _ ∈ blkMat n x.a (ddPart x.A X k.g true false false false) (ddPart x.A X k.g false true false false)
    refine mem_blkMat_iff_mem_of_same_block_and_mem_off.2 (fun i j => ⟨fun h => ?_, fun h => ?_⟩)
    · rw [mem_part]
      simp [NP.ρX, ep_algebraMap_eq_zero, ep'_algebraMap_eq_zero, eta_algebraMap_eq_zero]
    · have h0 : (mat x.ρ) g i j = 0 := by
        simpa using ((mem_blkMat_iff_mem_of_same_block_and_mem_off.1 (x.blk g)) i j).2 h
      rw [mem_part]
      simp [NP.ρX, h0]
  exact blk_mul act1 hP hZ

theorem UpperTheory.V.Pa.ok1 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X] (χ : G.Γ →* x.A), AdOk G.frame (fun g => k.ρ1 X (h.p₀ g)) (fun g => algebraMap x.A (DD X k.g) (χ g)) (W1 n x.A X k.g x.a) ∧ AdOk G.frame (fun g => k.ρ1 X (h.p₀ g)) (fun g => algebraMap x.A (DD X k.g) (χ g)) (pairedDualFirstOrderDualMatrixSpace n x.A X k.g x.a) ∧ AdOk G.frame (fun g => k.ρ1 X (h.p₀ g)) (fun g => algebraMap x.A (DD X k.g) (χ g)) (W2 n x.A X k.g x.a) := by
  intro l _ L G G0 h n x k X _ _ χ
  obtain ⟨r1, r2, r3, -, -⟩ := rho1 l G0.frame n x k X
  have hconj : ∀ g : G.frame.G₀, h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g) := by
    intro g
    apply Subtype.ext
    simp [Glob.Hom.p₀, GFrame.conj, h.c]
  have key : ∀ V₁ V₂ : Submodule x.A (DD X k.g),
      Act (ddPart x.A X k.g true false false false) (ddPart x.A X k.g false true false false) V₁ V₂ →
      AdOk G.frame (fun g => k.ρ1 X (h.p₀ g)) (fun g => algebraMap x.A (DD X k.g) (χ g)) (blkMat n x.a V₁ V₂) := by
    intro V₁ V₂ H
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show k.ρ1 X (h.p₀ 1) = 1
      rw [map_one]
      exact r1
    · intro a b
      show k.ρ1 X (h.p₀ (a * b)) = k.ρ1 X (h.p₀ a) * k.ρ1 X (h.p₀ b)
      rw [map_mul]
      exact r2 _ _
    · intro g
      refine ⟨Units.map (algebraMap x.A (DD X k.g) : x.A →* DD X k.g)
        ((G0.frame.eps ℤ_[l] x.A) (h.p₀ g) ^ (1 - (n : ℤ))), ?_⟩
      show (k.ρ1 X (h.p₀ g))ᵀ * k.ρ1 X (h.p₀ (G.frame.conj g)) = _
      rw [hconj, r3]
      rfl
    · show algebraMap x.A (DD X k.g) (χ 1) = 1
      simp
    · intro a b
      show algebraMap x.A (DD X k.g) (χ (a * b)) = algebraMap x.A (DD X k.g) (χ a) * algebraMap x.A (DD X k.g) (χ b)
      simp
    · intro g Z hZ
      show algebraMap x.A (DD X k.g) (χ g) • (k.ρ1 X (h.p₀ g) * Z * k.ρ1 X (h.p₀ g⁻¹)) ∈ _
      exact alg_smul_mem _ (blk_sand H (galois_lift_mem_first_order_deformations k X _) (galois_lift_mem_first_order_deformations k X _) hZ)
    · intro Z hZ
      show algebraMap x.A (DD X k.g) (χ G.frame.c) • Zᵀ ∈ _
      exact alg_smul_mem _ (blk_tr hZ)
  exact ⟨key _ _ act1, key _ _ act1s, key _ _ act2⟩
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.W

namespace UpperTheory.V.Pa

variable {l : ℕ} [Fact l.Prime] {Lc : Loc} {G : Glob l Lc} {q d : ℕ}

structure ArPres (a : ArData G q d) (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] where
  S : Set (HeightOneSpectrum (𝓞 F))
  above : ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S
  e : GS Ω S ≃ₜ* G.Γ
  e_ε : ∀ g, G.ε (e (toGS Ω S g)) = cycZ F Ω l g
  pl : ArData.W Lc q ≃ S
  pl_l : ∀ w, ((l : ℕ) : 𝓞 F) ∈ (pl w).1.asIdeal ↔ ∃ v, w = .inl v
  A : ArData.W Lc q → ValuationSubring Ω
  isOver : ∀ w, IsPlaceOver (A w) (pl w).1
  α : ∀ w, a.D w ≃ₜ* Dec (F := F) (A w)
  ι_eq : ∀ w g, a.ι w g = e (toGS Ω S (α w g : Formalism.ConjugateSelfDual.G F Ω))
  dv_eq : ∀ v, a.dv v = locDeg (pl (.inl v)).1
  ip : Fin d ≃ InfinitePlace F
  c : Fin d → Formalism.ConjugateSelfDual.G F Ω
  cc : ∀ i, IsCCAt (ip i) (c i)
  cw_eq : ∀ i, a.cw i = e (toGS Ω S (c i))

end UpperTheory.V.Pa
end
end

section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem linearMap_comp_eq_on_smul_of_eq (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (φ : ℤ_[l] →+* R)
    (h : ∀ y : R, l • y = 0) (τ : R →+ ZMod l) (a : ℤ_[l]) (y : R) :
    τ (φ a * y) = PadicInt.toZMod a * τ y := by
  have hspec := PadicInt.toZMod_spec a
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hspec
  obtain ⟨c, hc⟩ := hspec
  have ha : a = c * (l : ℤ_[l]) + ((PadicInt.toZMod a).val : ℤ_[l]) := by
    rw [hc, ZMod.cast_eq_val]
    ring
  have key : φ a * y = ((PadicInt.toZMod a).val : R) * y := by
    have e : φ a = φ c * (l : R) + ((PadicInt.toZMod a).val : R) := by
      rw [← map_natCast φ l, ← map_natCast φ, ← map_mul, ← map_add (f := _), ← ha]
    rw [e, add_mul, mul_assoc, ← nsmul_eq_mul l y, h y, mul_zero, zero_add]
  rw [key, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

private theorem hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l] (m : ℕ) :
    ∃ τ : (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k) ^ m}) →+ ZMod l,
      ∀ y, (∀ z, τ (y * z) = 0) → y = 0 := by
  cases m with
  | zero =>
    refine ⟨0, fun y _ => ?_⟩
    have htop : Ideal.span {(PowerSeries.X : PowerSeries k) ^ 0} = ⊤ := by
      rw [pow_zero, Ideal.span_singleton_one]
    exact (Ideal.Quotient.subsingleton_iff.2 htop).elim _ _
  | succ k0 =>
    letI := ZMod.algebra k l
    obtain ⟨lam, -, hlam, -⟩ := UpperTheory.V.AlgebraTools.frob_form_trunc (k := k) l k0
    exact ⟨lam, hlam⟩

theorem UpperTheory.V.Pa.pair1 :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (m : ℕ), ∃ τ : x.Am m →+ ZMod l, (∀ y, (∀ z, τ (y * z) = 0) → y = 0) ∧ ∀ (a : ℤ_[l]) y, τ (algebraMap x.A (x.Am m) (algebraMap ℤ_[l] x.A a) * y) = PadicInt.toZMod a * τ y := by
  intro l _ F n x m
  obtain ⟨-, -, -, h4, -, -, -, -, hc⟩ := finAm l F n x m 0
  obtain ⟨τ, hτ⟩ := hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero l x.K m
  exact ⟨τ, hτ, fun a y =>
    linearMap_comp_eq_on_smul_of_eq l (x.Am m) ((algebraMap x.A (x.Am m)).comp (algebraMap ℤ_[l] x.A)) h4 τ a y⟩
end
