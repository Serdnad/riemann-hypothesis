module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle008

@[expose] public section

section

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.FrameDict

theorem form_coords {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (cm : CMData F E) (W : Formalism.BasicNotions.HSpace E) (x y : Fin W.rank → E) :
    hE cm.sig W.gram x y = W.hT (∑ i, x i • W.frame i) (∑ i, y i • W.frame i) := by
  have hs : ∀ a : E, (cm.sig : E →+* E) a = star a := fun _ => rfl

  simp only [hE, Formalism.UG.hform, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, map_smul,
  LinearMap.smul_apply, smul_eq_mul, Formalism.BasicNotions.HSpace.gram, hs,
  Finset.mul_sum, starRingEnd_apply, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_one_iff {E : Type} [Field E] [NumberField E] (z : E) :
    z ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ z := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro h
    exact ⟨⟨z, h⟩, rfl⟩

theorem dict : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (W : HSpace E), (∀ a b : W.V, hE cm.sig W.gram (fun i => W.frame.repr a i) (fun i => W.frame.repr b i) = W.hT a b) ∧ ∃ L : Submodule (𝓞 E) (Fin W.rank → E), IsSelfDualLat cm.sig W.gram L ∧ (L : Set (Fin W.rank → E)) = latC W := by
  intro F E _ _ _ _ _ _ cm W
  refine ⟨fun a b => ?_, ?_⟩
  · rw [form_coords, W.frame.sum_repr, W.frame.sum_repr]
  obtain ⟨L, hfg, hsp, hL⟩ := exists_lattice W
  refine ⟨L, ⟨hfg, hsp, fun y => ?_⟩, hL⟩
  have hmem : ∀ x : Fin W.rank → E, x ∈ L ↔ ∑ i, x i • W.frame i ∈ W.L0 := fun x => by
    rw [← SetLike.mem_coe, hL]; rfl
  have hu : ∀ v : W.V, (∀ u ∈ W.L0, W.hT u v ∈ (1 : Submodule (𝓞 E) E)) ↔ v ∈ W.L0 := fun v => by
    have h : Formalism.HermitianLatticesTheory.dual W.hT W.L0 = W.L0 := W.baseLattice_isUnimodular
    conv_rhs => rw [← h]
    simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]
  rw [hmem, ← hu]
  constructor
  · intro h x hx
    rw [form_coords, ← mem_one_iff]
    exact h _ ((hmem x).1 hx)
  · intro h u hu'
    have := h (fun i => W.frame.repr u i) (by rw [hmem, W.frame.sum_repr]; exact hu')
    rw [form_coords, W.frame.sum_repr, ← mem_one_iff] at this
    exact this

end GlobalTheory.FrameDict
end

section

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.AdelicOrbit

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem parts_inj (x y : AF F ⊗[F] E)
    (h1 : (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom x =
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom y)
    (h2 : (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom x =
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom y) : x = y := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  exact e.injective (Prod.ext (((he x).1.trans h1).trans (he y).1.symm) (((he x).2.trans h2).trans (he y).2.symm))

theorem mem_parts (g : GL (Fin M) (AF F ⊗[F] E)) :
    g ∈ HR (AF F) σ J ↔
      Formalism.UG.bc (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom g ∈ HR (Ainf F) σ J ∧
      Formalism.UG.bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom g ∈ HR (Af F) σ J := by
  have := GlobalTheory.UnitarySplit.mem_iff _ _ (parts_inj (F := F) (E := E)) (sigR _ σ) (sigR _ σ) (sigR _ σ)
    (GlobalTheory.UnitarySplit.map_sig _ _) (GlobalTheory.UnitarySplit.map_sig _ _) (JR _ J) g
  rw [GlobalTheory.UnitarySplit.map_JR, GlobalTheory.UnitarySplit.map_JR] at this
  exact this

theorem exists_fin (h : HA (AF F) σ J) :
    ∃ k : HA (Af F) σ J, (HA.mat (Af F) σ J k).1 = finMat σ J h :=
  ⟨(⟨_, ((mem_parts σ J (HA.mat (AF F) σ J h)).1 h.2).2⟩ : HR (Af F) σ J), rfl⟩

theorem exists_lift (k : HA (Af F) σ J) :
    ∃ h : HA (AF F) σ J, finMat σ J h = (HA.mat (Af F) σ J k).1 ∧
      (HA.mat (AF F) σ J h).1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom = 1 := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have hs : ∀ a b, ∃ x, (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom x = a ∧
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom x = b := fun a b => by
    refine ⟨e.symm (a, b), (he _).1.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp
  obtain ⟨g, g1, g2⟩ := GlobalTheory.UnitarySplit.gl_glue _ _ parts_inj hs 1 (HA.mat (Af F) σ J k)
  have hg : g ∈ HR (AF F) σ J := (mem_parts σ J g).2 ⟨g1 ▸ one_mem _, g2 ▸ k.2⟩
  exact ⟨(⟨g, hg⟩ : HR (AF F) σ J), congrArg Units.val g2, congrArg Units.val g1⟩

omit [NumberField E] in
theorem projFin_smul (h : HA (AF F) σ J) (x : Fin 1 → Fin M → E) :
    projFin (h • ratTup (F := F) (AF F) x) 0 = finMat σ J h *ᵥ fun i => inclR (F := F) (Af F) (x 0 i) := by
  funext i
  have := RingHom.map_mulVec (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
    (HA.mat (AF F) σ J h).1 (fun i => inclR (F := F) (AF F) (x 0 i)) i
  refine this.trans ?_
  congr 1

omit [NumberField E] in
theorem projInf_smul (h : HA (AF F) σ J) (x : Fin 1 → Fin M → E) (i : Fin M) :
    (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom ((h • ratTup (F := F) (AF F) x) 0 i) =
      ((HA.mat (AF F) σ J h).1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom *ᵥ
        fun i => inclR (F := F) (Ainf F) (x 0 i)) i := by
  have := RingHom.map_mulVec (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
    (HA.mat (AF F) σ J h).1 (fun i => inclR (F := F) (AF F) (x 0 i)) i
  refine this.trans ?_
  congr 1

end SlopeTestRemainingChoices

theorem mem_latHat_iff : StabTransitive → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ L : Submodule (𝓞 E) (Fin M → E), IsSelfDualLat σ J L → ∀ β : F, (β = 1 ∨ β = -1) → ∀ x : Fin 1 → Fin M → E, x 0 ∈ L → hE σ J (x 0) (x 0) = algebraMap F E β → ∀ h : HA (AF F) σ J, projFin (h⁻¹ • ratTup (F := F) (AF F) x) 0 ∈ latHat F E (L : Set (Fin M → E)) ↔ ∃ a ∈ Hstab (AF F) σ J x, a⁻¹ * h ∈ stab σ J (L : Set (Fin M → E)) := by
  intro hT F E _ _ _ _ _ σ hcm hur M J hJ L hL β hβ x hx hq h
  constructor
  · intro hm
    have hO := (hT F E σ hcm hur M J hJ L hL β hβ (x 0) hx hq).2.1
    obtain ⟨k', hk'⟩ := exists_fin σ J h⁻¹
    have h1 : k'⁻¹ ∈ {h : HA (Af F) σ J | actV (Af F) σ J h⁻¹ (fun i => inclR (F := F) (Af F) (x 0 i)) ∈
        latHat F E (L : Set (Fin M → E))} := by
      rw [Set.mem_setOf_eq, inv_inv, actV_eq, hk', ← projFin_smul]
      exact hm
    rw [hO] at h1
    obtain ⟨af, haf, kf, hkf, e⟩ := h1
    obtain ⟨a, ha1, ha2⟩ := exists_lift σ J af
    refine ⟨a, ?_, ?_⟩
    · change a • ratTup (F := F) (AF F) x = ratTup (F := F) (AF F) x
      funext c i
      obtain rfl : c = 0 := Subsingleton.elim _ _
      refine parts_inj _ _ ?_ ?_
      · rw [projInf_smul, ha2, Matrix.one_mulVec]
        rfl
      · have h2 := congrFun (projFin_smul σ J a x) i
        rw [ha1] at h2
        refine h2.trans ?_
        have h3 : af • ratTup (F := F) (Af F) (fun _ : Fin 1 => x 0) = ratTup (F := F) (Af F) (fun _ => x 0) := haf
        exact congrFun (congrFun h3 0) i
    · have e' : k' * af = kf⁻¹ := by
        have e2 : af * kf = k'⁻¹ := e
        rw [← inv_inv k', ← e2]
        group
      have h2 : h⁻¹ * a ∈ stab σ J (L : Set (Fin M → E)) := by
        intro y
        rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, ha1, ← hk', ← Matrix.mulVec_mulVec, ← actV_eq, ← actV_eq, ← actV_mul, e']
        exact (inv_mem hkf : kf⁻¹ ∈ stabLat (Af F) σ J (latHat F E (L : Set (Fin M → E)))) y
      have h3 := inv_mem h2
      rwa [_root_.mul_inv_rev, inv_inv] at h3
  · rintro ⟨a, ha, hk⟩
    have h1 : a⁻¹ • ratTup (F := F) (AF F) x = ratTup (F := F) (AF F) x := inv_mem ha
    have h2 : h⁻¹ • ratTup (F := F) (AF F) x = (a⁻¹ * h)⁻¹ • ratTup (F := F) (AF F) x := by
      conv_rhs => rw [← h1, ← mul_smul]
      congr 1
      group
    rw [h2, projFin_smul]
    exact ((inv_mem hk : (a⁻¹ * h)⁻¹ ∈ stab σ J (L : Set (Fin M → E))) _).1
      (AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, x 0, hx, rfl⟩)

end GlobalTheory.AdelicOrbit
end

section

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.StabFrame

section Lin

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem exists_mulVec_eq (σ : E →ₐ[F] E) {M M' : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (B : Matrix (Fin M) (Fin M') E) (N : Matrix (Fin M') (Fin M) E) (hN : N * B = 1) (x : Fin M → E)
    (hM : M' + 1 = M) (hB : ∀ j, hE σ J x (fun i => B i j) = 0) (hx : hE σ J x x ≠ 0) :
    (∀ z, hE σ J x (B *ᵥ z) = 0) ∧ ∀ y, hE σ J x y = 0 → B *ᵥ (N *ᵥ y) = y := by
  let φ : (Fin M → E) →ₗ[E] E :=
    { toFun := fun y => hE σ J x y
      map_add' := fun y z => by
        simp only [hE, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c y => by
        simp only [hE, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring }
  have hle : LinearMap.range B.mulVecLin ≤ LinearMap.ker φ := by
    rw [Matrix.range_mulVecLin, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hB j
  have hinj : Function.Injective B.mulVecLin := fun z w h => by
    have := congrArg (N *ᵥ ·) h
    simpa [Matrix.mulVec_mulVec, hN] using this
  have h1 : Module.finrank E (LinearMap.range B.mulVecLin) = M' := by
    rw [LinearMap.finrank_range_of_inj hinj]; simp
  have hlt : LinearMap.ker φ < ⊤ := lt_top_iff_ne_top.2 fun h => hx (by
    have : x ∈ LinearMap.ker φ := h ▸ Submodule.mem_top
    exact this)
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt
  rw [finrank_top, Module.finrank_fin_fun] at h2
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  refine ⟨fun z => hle ⟨z, rfl⟩, fun y hy => ?_⟩
  have : y ∈ LinearMap.range B.mulVecLin := heq ▸ hy
  obtain ⟨z, rfl⟩ := this
  simp [Matrix.mulVec_mulVec, hN]

theorem map_mulVec_tmul (R : Type) [CommRing R] [Algebra F R] {m n : ℕ} (C : Matrix (Fin m) (Fin n) E)
    (a : R) (z : Fin n → E) :
    C.map (inclR (F := F) R) *ᵥ (fun i => a ⊗ₜ[F] z i) = fun i => a ⊗ₜ[F] (C *ᵥ z) i := by
  funext i
  simp [Matrix.mulVec, dotProduct, inclR, TensorProduct.tmul_sum]

variable [NumberField F]

theorem mulVec_mem_latHat {m n : ℕ} (C : Matrix (Fin m) (Fin n) E) {S : Set (Fin n → E)}
    {T : Set (Fin m → E)} (h : ∀ z ∈ S, C *ᵥ z ∈ T) {y : Fin n → Af F ⊗[F] E} (hy : y ∈ latHat F E S) :
    C.map (inclR (F := F) (Af F)) *ᵥ y ∈ latHat F E T := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨a, ha, _, h z hz, map_mulVec_tmul _ C a z⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
  | neg y _ hy => rw [Matrix.mulVec_neg]; exact neg_mem hy

theorem mulVec_eq_of_mem_latHat {n : ℕ} (C : Matrix (Fin n) (Fin n) E) {S : Set (Fin n → E)}
    (h : ∀ z ∈ S, C *ᵥ z = z) {y : Fin n → Af F ⊗[F] E} (hy : y ∈ latHat F E S) :
    C.map (inclR (F := F) (Af F)) *ᵥ y = y := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hy
    rw [map_mulVec_tmul, h z hz]
  | zero => rw [Matrix.mulVec_zero]
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, hy, hz]
  | neg y _ hy => rw [Matrix.mulVec_neg, hy]

theorem stabHat_iff {M M' : ℕ} (B : Matrix (Fin M) (Fin M') E) (N : Matrix (Fin M') (Fin M) E)
    (hN : N * B = 1) {P : Set (Fin M → E)} {L' : Set (Fin M' → E)} (h1 : ∀ z, z ∈ L' ↔ B *ᵥ z ∈ P)
    (h2 : ∀ y ∈ P, B *ᵥ (N *ᵥ y) = y) (a b : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))
    (a' b' : Matrix (Fin M') (Fin M') (Af F ⊗[F] E)) (hb : b * a = 1) (hb' : a' * b' = 1)
    (hr : a * B.map (inclR (F := F) (Af F)) = B.map (inclR (F := F) (Af F)) * a') :
    StabHat F P a ↔ StabHat F L' a' := by
  set Bf := B.map (inclR (F := F) (Af F)) with hBf
  set Nf := N.map (inclR (F := F) (Af F)) with hNf
  have hNB : Nf * Bf = 1 := by
    rw [hBf, hNf, ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBm : ∀ z ∈ latHat F E L', Bf *ᵥ z ∈ latHat F E P := fun z hz =>
    mulVec_mem_latHat B (fun w hw => (h1 w).1 hw) hz
  have hNm : ∀ y ∈ latHat F E P, Nf *ᵥ y ∈ latHat F E L' := fun y hy =>
    mulVec_mem_latHat N (fun w hw => (h1 _).2 (by rw [h2 w hw]; exact hw)) hy
  have hBN : ∀ y ∈ latHat F E P, Bf *ᵥ (Nf *ᵥ y) = y := fun y hy => by
    rw [Matrix.mulVec_mulVec, hBf, hNf, ← Matrix.map_mul]
    exact mulVec_eq_of_mem_latHat _ (fun w hw => by rw [← Matrix.mulVec_mulVec]; exact h2 w hw) hy
  have hiff : ∀ z, z ∈ latHat F E L' ↔ Bf *ᵥ z ∈ latHat F E P := fun z =>
    ⟨hBm z, fun hz => by simpa [Matrix.mulVec_mulVec, hNB] using hNm _ hz⟩
  have hcomm : ∀ z, a *ᵥ (Bf *ᵥ z) = Bf *ᵥ (a' *ᵥ z) := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hr]
  refine ⟨fun h z => ?_, fun h y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · rw [hiff, hiff, ← hcomm]
    exact h _
  · rw [← hBN y hy, hcomm]
    exact hBm _ ((h _).1 (hNm y hy))
  · have e1 : a' *ᵥ (b' *ᵥ (Nf *ᵥ (a *ᵥ y))) = Nf *ᵥ (a *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, hb', Matrix.one_mulVec]
    have e2 : y = Bf *ᵥ (b' *ᵥ (Nf *ᵥ (a *ᵥ y))) := by
      have := congrArg (b *ᵥ ·) (hcomm (b' *ᵥ (Nf *ᵥ (a *ᵥ y))))
      simp only [e1, hBN _ hy] at this
      rw [Matrix.mulVec_mulVec _ b a, Matrix.mulVec_mulVec _ b a, hb, Matrix.one_mulVec,
        Matrix.one_mulVec] at this
      exact this.symm
    rw [e2]
    exact hBm _ ((h _).2 (by rw [e1]; exact hNm _ hy))

def finPt (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : HA (AF F) σ J) : HA (Af F) σ J :=
  (⟨Formalism.UG.bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom (HA.mat (AF F) σ J g), by
    have hg : Formalism.UG.cT (sigR (AF F) σ) (HA.mat (AF F) σ J g).1 * JR (AF F) J * (HA.mat (AF F) σ J g).1 =
      JR (AF F) J := (show HR (AF F) σ J from g).2
    have := GlobalTheory.UnitarySplit.map_cond _ _ _ (GlobalTheory.UnitarySplit.map_sig (sndA F) σ) (JR (AF F) J)
      (HA.mat (AF F) σ J g).1
    rw [hg, GlobalTheory.UnitarySplit.map_JR] at this
    exact this.symm⟩ : HR (Af F) σ J)

theorem map_snd_incl {m n : ℕ} (C : Matrix (Fin m) (Fin n) E) :
    (C.map (inclR (F := F) (AF F))).map (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom =
      C.map (inclR (F := F) (Af F)) := by
  ext i j
  simp [inclR]

end Lin

theorem stab_iff_of_frameRel : StabTransitive → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E → ∀ (M M' : ℕ) (J : Matrix (Fin M) (Fin M) E) (J' : Matrix (Fin M') (Fin M') E) (B : Matrix (Fin M) (Fin M') E) (x : Fin 1 → Fin M → E), M' + 1 = M → IsHermND σ J → IsHermND σ J' → Formalism.UG.cT (σ : E →+* E) B * J * B = J' → (∀ j, hE σ J (x 0) (fun i => B i j) = 0) → hE σ J (x 0) (x 0) ≠ 0 → ∀ (L : Submodule (𝓞 E) (Fin M → E)) (L' : Set (Fin M' → E)), IsSelfDualLat σ J L → ∀ β : F, (β = 1 ∨ β = -1) → x 0 ∈ L → hE σ J (x 0) (x 0) = algebraMap F E β → (∀ y, y ∈ L' ↔ B *ᵥ y ∈ L) → ∀ (g : HA (AF F) σ J) (g' : HA (AF F) σ J'), g ∈ Hstab (AF F) σ J x → FrameRel J J' B g g' → (g ∈ stab σ J (L : Set (Fin M → E)) ↔ g' ∈ stab σ J' L') := by
  intro H F E _ _ _ _ _ σ hCM hu M M' J J' B x hM hJ hJ' hBJ hB hx L L' hL β hβ hxL hq hL' g g' hg hr
  let p := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  have hN : (J'⁻¹ * (Formalism.UG.cT (σ : E →+* E) B * J)) * B = 1 := by
    rw [Matrix.mul_assoc, hBJ, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hJ'.2)]
  obtain ⟨k1, k2⟩ := exists_mulVec_eq σ J B _ hN (x 0) hM hB hx
  have h3 := (H F E σ hCM hu M J hJ L hL β hβ (x 0) hxL hq).2.2
  have hgf : finPt σ J g ∈ Hstab (Af F) σ J (fun _ => x 0) := by
    have e : (HA.mat (AF F) σ J g).1 *ᵥ (fun i => inclR (AF F) (x 0 i)) = fun i => inclR (AF F) (x 0 i) :=
      congrFun (MulAction.mem_stabilizer_iff.1 hg) 0
    have e' : (p ∘ fun i => inclR (AF F) (x 0 i)) = fun i => inclR (Af F) (x 0 i) := by
      funext i
      simp [p, inclR]
    refine MulAction.mem_stabilizer_iff.2 (funext fun _ => funext fun i => ?_)
    have := RingHom.map_mulVec p (HA.mat (AF F) σ J g).1 (fun i => inclR (AF F) (x 0 i)) i
    rw [e, e'] at this
    exact this.symm.trans (congrFun e' i)
  have h4 : StabHat F (L : Set (Fin M → E)) (finMat σ J g) ↔
      StabHat F (perpIn σ J L (x 0)) (finMat σ J g) := by
    have := SetLike.ext_iff.1 h3 (finPt σ J g)
    rw [Subgroup.mem_inf, Subgroup.mem_inf, and_iff_left hgf, and_iff_left hgf] at this
    exact this
  refine h4.trans (stabHat_iff (P := perpIn σ J L (x 0)) B _ hN (fun z => (hL' z).trans ⟨fun h => ⟨h, k1 z⟩, fun h => h.1⟩)
    (fun y hy => k2 y hy.2) _ (finMat σ J g⁻¹) _ (finMat σ J' g'⁻¹) ?_ ?_ ?_)
  · rw [← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, inv_mul_cancel, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one]
  · rw [← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, mul_inv_cancel, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one]
  · have : ((HA.mat (AF F) σ J g).1 * B.map (inclR (AF F))).map p =
        (B.map (inclR (AF F)) * (HA.mat (AF F) σ J' g').1).map p := congrArg (fun X => Matrix.map X p) hr
    have := (Matrix.map_mul (f := p)).symm.trans (this.trans (Matrix.map_mul (f := p)))
    rw [map_snd_incl] at this
    exact this

end GlobalTheory.StabFrame
end
end
