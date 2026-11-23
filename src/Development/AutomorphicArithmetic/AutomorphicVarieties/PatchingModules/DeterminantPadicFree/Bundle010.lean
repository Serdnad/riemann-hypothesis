module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle002
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
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.FieldTheory.Finite.GaloisField

@[expose] public section

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.w1sMem :
    ∀ {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ}, (∀ Z : Matrix (Fin n) (Fin n) (DD X g), Z ∈ pairedDualFirstOrderDualMatrixSpace n A X g a → etaM Z ∈ Ev A X n a ∧ ∀ j, ep'M j Z ∈ Od A X n a) ∧ (∀ Z ∈ pairedDualFirstOrderDualMatrixSpace n A X g a, ∀ Z' ∈ pairedDualFirstOrderDualMatrixSpace n A X g a, etaM Z = etaM Z' → (∀ j, ep'M j Z = ep'M j Z') → Z = Z') ∧ ∀ (Y₀ : Matrix (Fin n) (Fin n) X) (Y : Fin g → Matrix (Fin n) (Fin n) X), Y₀ ∈ Ev A X n a → (∀ j, Y j ∈ Od A X n a) → ∃ Z ∈ pairedDualFirstOrderDualMatrixSpace n A X g a, etaM Z = Y₀ ∧ ∀ j, ep'M j Z = Y j := by
  intro A X _ _ _ g n a
  have hW : ∀ Z : Matrix (Fin n) (Fin n) (DD X g), Z ∈ pairedDualFirstOrderDualMatrixSpace n A X g a ↔ ∀ i j : Fin n,
      ((↑i < a ↔ ↑j < a) → (Z i j).a = 0 ∧ (Z i j).ep = 0 ∧ (Z i j).ep' = 0) ∧
      (¬(↑i < a ↔ ↑j < a) → (Z i j).a = 0 ∧ (Z i j).ep = 0 ∧ (Z i j).eta = 0) := by
    intro Z
    simp [pairedDualFirstOrderDualMatrixSpace, blkMat, ddPart]
  have hE : ∀ Y : Matrix (Fin n) (Fin n) X, Y ∈ Ev A X n a ↔
      ∀ i j : Fin n, ¬(↑i < a ↔ ↑j < a) → Y i j = 0 := by
    intro Y
    simp [Ev, blkMat]
  have hO : ∀ Y : Matrix (Fin n) (Fin n) X, Y ∈ Od A X n a ↔
      ∀ i j : Fin n, (↑i < a ↔ ↑j < a) → Y i j = 0 := by
    intro Y
    simp [Od, blkMat]
  refine ⟨?_, ?_, ?_⟩
  · intro Z hZ
    rw [hW] at hZ
    refine ⟨(hE _).2 fun i j hij => ((hZ i j).2 hij).2.2, fun l => (hO _).2 fun i j hij => ?_⟩
    simp only [ep'M, Matrix.map_apply]
    rw [((hZ i j).1 hij).2.2]
    rfl
  · intro Z hZ Z' hZ' he hp
    rw [hW] at hZ hZ'
    funext i j
    have h1 := congrFun (congrFun he i) j
    have h2 : ∀ l, (Z i j).ep' l = (Z' i j).ep' l := fun l => congrFun (congrFun (hp l) i) j
    simp only [etaM, Matrix.map_apply] at h1
    have ha : (Z i j).a = (Z' i j).a ∧ (Z i j).ep = (Z' i j).ep := by
      by_cases hij : (↑i < a ↔ ↑j < a)
      · rw [((hZ i j).1 hij).1, ((hZ' i j).1 hij).1, ((hZ i j).1 hij).2.1, ((hZ' i j).1 hij).2.1]
        exact ⟨rfl, rfl⟩
      · rw [((hZ i j).2 hij).1, ((hZ' i j).2 hij).1, ((hZ i j).2 hij).2.1, ((hZ' i j).2 hij).2.1]
        exact ⟨rfl, rfl⟩
    exact DD.ext ha.1 ha.2 (funext h2) h1
  · intro Y₀ Y h0 hY
    rw [hE] at h0
    refine ⟨Matrix.of fun i j => ⟨0, 0, fun l => Y l i j, Y₀ i j⟩, (hW _).2 fun i j =>
      ⟨fun hij => ⟨rfl, rfl, funext fun l => (hO _).1 (hY l) i j hij⟩, fun hij => ⟨rfl, rfl, h0 i j hij⟩⟩,
      rfl, fun l => rfl⟩
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem mapL {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (j : A →+* B) (p : B →+ A)
    (hp : ∀ a y, p (j a * y) = a * p y) (M : Matrix (Fin n) (Fin n) A) (Z : Matrix (Fin n) (Fin n) B) :
    (M.map j * Z).map p = M * Z.map p := by
  ext a b

  simp [Matrix.mul_apply, map_sum, hp]

private theorem mapR {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (j : A →+* B) (p : B →+ A)
    (hp : ∀ a y, p (j a * y) = a * p y) (M : Matrix (Fin n) (Fin n) A) (Z : Matrix (Fin n) (Fin n) B) :
    (Z * M.map j).map p = Z.map p * M := by
  ext a b

  simp only [Matrix.mul_apply, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm, hp, mul_comm]

theorem UpperTheory.V.Pa.Det.compSel :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A), x.Ext2 x' j → ∀ (p : x'.A →+ x.A), (∀ a y, p (j a * y) = a * p y) → (∀ N : ℕ, ∃ N' : ℕ, ∀ y ∈ Ideal.span {x'.t} ^ N', p y ∈ Ideal.span {x.t} ^ N) → (∀ z ∈ SelZ F x'.t (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (Od x'.A x'.A n x'.a), (fun g => (z g).map p) ∈ SelZ F x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a)) ∧ ∀ z ∈ Bd F (x'.ρX x'.A) (Od x'.A x'.A n x'.a), (fun g => (z g).map p) ∈ Bd F (x.ρX x.A) (Od x.A x.A n x.a) := by
  intro l _ F n x x' j hE p hp hc
  obtain ⟨⟨-, -, -, hρ, ha, -⟩, hw, -⟩ := hE
  have e1 : ∀ g, x'.ρX x'.A g = (x.ρX x.A g).map j := by
    intro g
    ext a b
    simp [NP.ρX, hρ, mat]
  have e2 : ∀ v, x'.wX x'.A v = (x.wX x.A v).map j := by
    intro v
    ext a b
    simp [NP.wX, hw]
  have e3 : ∀ v, x'.wiX x'.A v = (x.wiX x.A v).map j := by
    intro v
    ext a b
    simp only [NP.wiX, hw, ← map_inv]
    rfl
  have hOd : ∀ Y ∈ Od x'.A x'.A n x'.a, Y.map p ∈ Od x.A x.A n x.a := by
    intro Y hY a b
    refine ⟨fun h => ?_, fun _ => trivial⟩
    have := (hY a b).1 (by rw [ha]; exact h)
    rw [Submodule.mem_bot] at this ⊢
    simp [this]
  have hsub : ∀ Y Z : Matrix (Fin n) (Fin n) x'.A, (Y - Z).map p = Y.map p - Z.map p := by
    intro Y Z; ext a b; simp
  have hadd : ∀ Y Z : Matrix (Fin n) (Fin n) x'.A, (Y + Z).map p = Y.map p + Z.map p := by
    intro Y Z; ext a b; simp
  have hd : ∀ Y g, (dY F (x'.ρX x'.A) Y g).map p = dY F (x.ρX x.A) (Y.map p) g := by
    intro Y g
    simp only [dY]
    rw [hsub, e1, e1, mapR j p hp, mapL j p hp]
  refine ⟨?_, ?_⟩
  · rintro z ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨fun g => hOd _ (h1 g), ?_, ?_, ?_, ?_, ?_⟩
    · intro a b N
      obtain ⟨N', hN⟩ := hc N
      have := h2 a b N'
      rw [IsLocallyConstant.iff_eventually_eq] at this ⊢
      intro g
      filter_upwards [this g] with h hh
      rw [Ideal.Quotient.eq] at hh ⊢
      have := hN _ hh
      rw [map_sub] at this
      exact this
    · intro g h
      simp only
      rw [h3, hadd, e1, e1, mapR j p hp, mapL j p hp]
    · intro g
      simp only
      rw [h4]
      ext a b
      simp
    · intro u g hg
      simp only
      rw [h5 u g hg]
      ext a b
      simp
    · intro v
      obtain ⟨Y, hY, hL⟩ := h6 v
      refine ⟨Y.map p, hOd _ hY, fun g => ?_⟩
      have key : x.wiX x.A v * ((z (F.φ v g)).map p - dY F (x.ρX x.A) (Y.map p) (F.φ v g)) * x.wX x.A v =
          (x'.wiX x'.A v * (z (F.φ v g) - dY F (x'.ρX x'.A) Y (F.φ v g)) * x'.wX x'.A v).map p := by
        rw [e2, e3, mapR j p hp, mapL j p hp, hsub, hd]
      refine ⟨fun a b hab => ?_, fun hg a => ?_⟩
      · simp only
        rw [key, Matrix.map_apply, (hL g).1 a b hab, map_zero]
      · simp only
        rw [key, Matrix.map_apply, (hL g).2 hg a, map_zero]
  · rintro z ⟨Y, hY, hT, rfl⟩
    refine ⟨Y.map p, hOd _ hY, ?_, funext fun g => hd Y g⟩
    ext a b
    have := congrFun (congrFun hT a) b
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    simp [this]
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.dSigma :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (χ : G → F) (Y : Matrix (Fin n) (Fin n) F) (g : G), (∀ g, χ (D.σ g) = χ g) → dTw χ D.r Y (D.σ g) = (dTw χ D.r Yᵀ g)ᵀ := by
  intro F G _ _ n D χ Y g hχ
  have e1 : D.r (D.σ g) = (D.μ g : F) • (D.r g⁻¹)ᵀ := by
    have h : (D.r g⁻¹)ᵀ * (D.r g)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← map_mul, mul_inv_cancel, map_one, Matrix.transpose_one]
    calc D.r (D.σ g) = (D.r g⁻¹)ᵀ * ((D.r g)ᵀ * D.r (D.σ g)) := by
          rw [← Matrix.mul_assoc, h, Matrix.one_mul]
      _ = _ := by rw [D.form, Matrix.mul_smul, Matrix.mul_one]
  have e2 : D.r (D.σ g)⁻¹ = (D.μ g⁻¹ : F) • (D.r g)ᵀ := by
    have h : (D.r g)ᵀ * (D.r g⁻¹)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← map_mul, inv_mul_cancel, map_one, Matrix.transpose_one]
    rw [← map_inv]
    calc D.r (D.σ g⁻¹) = (D.r g)ᵀ * ((D.r g⁻¹)ᵀ * D.r (D.σ g⁻¹)) := by
          rw [← Matrix.mul_assoc, h, Matrix.one_mul]
      _ = _ := by rw [D.form, Matrix.mul_smul, Matrix.mul_one]
  have e3 : ((D.μ g : F) * D.μ g⁻¹) • (1 : Matrix (Fin n) (Fin n) F) = 1 := by
    have h : D.r (D.σ g) * D.r (D.σ g)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [e1, e2, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.transpose_mul, ← map_mul, mul_inv_cancel,
      map_one, Matrix.transpose_one, smul_smul] at h
    exact h
  have key : D.r (D.σ g) * Y * D.r (D.σ g)⁻¹ = (D.r g⁻¹)ᵀ * Y * (D.r g)ᵀ := by
    rw [e1, e2, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show ((D.μ g : F) * D.μ g⁻¹) • ((D.r g⁻¹)ᵀ * Y * (D.r g)ᵀ)
        = (((D.μ g : F) * D.μ g⁻¹) • (1 : Matrix (Fin n) (Fin n) F)) * ((D.r g⁻¹)ᵀ * Y * (D.r g)ᵀ) by
      rw [Matrix.smul_mul, Matrix.one_mul], e3, Matrix.one_mul]
  simp only [dTw, hχ, key, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc]
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.extTrans :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' x'' : NP F n) (j : x.A →+* x'.A) (j' : x'.A →+* x''.A), x.Ext2 x' j → x'.Ext2 x'' j' → x.Ext2 x'' (j'.comp j) := by
  intro l _ F n x x' x'' j j' h1 h2
  obtain ⟨⟨hi, hl, hf, hρ, ha, hψ⟩, hw, ht⟩ := h1
  obtain ⟨⟨hi', hl', hf', hρ', ha', hψ'⟩, hw', ht'⟩ := h2
  refine ⟨⟨hi'.comp hi, @RingHom.isLocalHom_comp _ _ _ _ _ _ j' j hl' hl, hf'.comp hf, ?_, ha'.trans ha, ?_⟩,
    ?_, ht'.trans ht⟩
  · rw [hρ', hρ]
    simp only [pushRep, GeneralLinearGroup.map_comp, MonoidHom.comp_assoc]
  · intro v i
    rw [hψ', hψ]
    ext g
    simp [pushCh]
  · intro v
    rw [hw', hw, GeneralLinearGroup.map_comp]
    rfl
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem adicCont_map {Γ R S : Type} [TopologicalSpace Γ] [CommRing R] [CommRing S] (j : R →+* S)
    (I : Ideal R) (J : Ideal S) (h : I.map j ≤ J) (f : Γ → R) (hf : AdicCont I f) :
    AdicCont J fun g => j (f g) := by
  intro N
  have hN : I ^ N ≤ (J ^ N).comap j := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono h N
  exact (hf N).comp (Ideal.quotientMap (J ^ N) j hN)

private theorem od_map {R S : Type} [CommRing R] [CommRing S] (j : R →+* S) {n a : ℕ}
    {Z : Matrix (Fin n) (Fin n) R} (h : Z ∈ Od R R n a) : Z.map j ∈ Od S S n a := by
  intro i k
  refine ⟨fun e => ?_, fun _ => Submodule.mem_top⟩
  have := (h i k).1 e
  rw [Submodule.mem_bot] at this ⊢
  simp [this]

theorem UpperTheory.V.Pa.Det.pushSel :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A), x.Ext2 x' j → (∀ z ∈ SelZ F x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a), (fun g => (z g).map j) ∈ SelZ F x'.t (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (Od x'.A x'.A n x'.a)) ∧ (∀ z ∈ Bd F (x.ρX x.A) (Od x.A x.A n x.a), (fun g => (z g).map j) ∈ Bd F (x'.ρX x'.A) (Od x'.A x'.A n x'.a)) ∧ ∀ z v Y, LocAt F (x.ρX x.A) (x.wX x.A) (x.wiX x.A) z v Y → LocAt F (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (fun g => (z g).map j) v (Y.map j) := by
  intro l _ F n x x' j hE
  obtain ⟨⟨-, hloc, -, hρ, ha, -⟩, hw, -⟩ := hE
  have eρ : ∀ g, x'.ρX x'.A g = j.mapMatrix (x.ρX x.A g) := by
    intro g
    ext i k : 1
    simp only [NP.ρX, hρ]
    rfl
  have ew : ∀ v, x'.wX x'.A v = j.mapMatrix (x.wX x.A v) := by
    intro v
    ext i k : 1
    simp only [NP.wX, hw]
    rfl
  have ewi : ∀ v, x'.wiX x'.A v = j.mapMatrix (x.wiX x.A v) := by
    intro v
    ext i k : 1
    simp only [NP.wiX, hw, ← map_inv]
    rfl
  have ed : ∀ Y g, dY F (x'.ρX x'.A) (Y.map j) g = j.mapMatrix (dY F (x.ρX x.A) Y g) := by
    intro Y g
    simp only [dY, eρ, map_sub, map_mul]
    rfl
  have hL : ∀ z v Y, LocAt F (x.ρX x.A) (x.wX x.A) (x.wiX x.A) z v Y →
      LocAt F (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (fun g => (z g).map j) v (Y.map j) := by
    intro z v Y h g
    have key : x'.wiX x'.A v * ((z (F.φ v g)).map j - dY F (x'.ρX x'.A) (Y.map j) (F.φ v g)) * x'.wX x'.A v
        = j.mapMatrix (x.wiX x.A v * (z (F.φ v g) - dY F (x.ρX x.A) Y (F.φ v g)) * x.wX x.A v) := by
      rw [ed, ew, ewi, map_mul, map_mul, map_sub]
      rfl
    refine ⟨fun i k hik => ?_, fun hg i => ?_⟩
    · simp only [key, RingHom.mapMatrix_apply, Matrix.map_apply, (h g).1 i k hik, map_zero]
    · simp only [key, RingHom.mapMatrix_apply, Matrix.map_apply, (h g).2 hg i, map_zero]
  have ht : (Ideal.span {algebraMap x.A x.A x.t}).map j ≤ Ideal.span {algebraMap x'.A x'.A x'.t} := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    change (PowerSeries.X : PowerSeries x'.K) ∣ j PowerSeries.X
    rw [PowerSeries.X_dvd_iff]
    by_contra hne
    have hu : IsUnit (j PowerSeries.X) := PowerSeries.isUnit_iff_constantCoeff.2 (Ne.isUnit hne)
    have hX := PowerSeries.isUnit_iff_constantCoeff.1 (hloc.map_nonunit _ hu)
    simp at hX
  refine ⟨?_, ?_, hL⟩
  · rintro z ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨fun g => ha ▸ od_map j (h1 g), fun i k => adicCont_map j _ _ ht _ (h2 i k), fun g h => ?_,
      fun g => ?_, fun u g hg => ?_, fun v => ?_⟩
    · change j.mapMatrix (z (g * h)) = j.mapMatrix (z g) + _ * j.mapMatrix (z h) * _
      rw [h3, eρ, eρ, map_add (f := _), map_mul, map_mul]
    · ext i k : 1
      simp [h4]
    · simp [h5 u g hg]
    · obtain ⟨Y, hY, hl⟩ := h6 v
      exact ⟨Y.map j, ha ▸ od_map j hY, hL z v Y hl⟩
  · rintro z ⟨Y, hY, hT, rfl⟩
    refine ⟨Y.map j, ha ▸ od_map j hY, ?_, ?_⟩
    · rw [← Matrix.transpose_map, hT]
      ext i k : 1
      simp
    · funext g
      exact (ed Y g).symm
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem map_finite {K L : Type} [Field K] [Field L] [Finite L] (f : K →+* L) :
    (PowerSeries.map f).Finite := by
  classical
  letI := f.toAlgebra
  letI := (PowerSeries.map f).toAlgebra
  haveI : Module.Finite K L := Module.Finite.of_finite
  let b := Module.finBasis K L
  show Module.Finite (PowerSeries K) (PowerSeries L)
  refine ⟨⟨Finset.univ.image (fun i => PowerSeries.C (b i)), ?_⟩⟩
  rw [eq_top_iff]
  intro φ _
  have key : φ = ∑ i, (PowerSeries.mk fun n => b.repr (PowerSeries.coeff n φ) i) •
      PowerSeries.C (b i) := by
    ext n

    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_sum, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_map, PowerSeries.coeff_mk]
    exact (b.sum_repr _).symm.trans (Finset.sum_congr rfl fun i _ => Algebra.smul_def _ _)
  rw [key]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp

private theorem bijective_residue_comp_powerSeries_C (F : Type) [Field F] :
    Function.Bijective ((residue (PowerSeries F)).comp (PowerSeries.C (R := F))) := by
  refine ⟨RingHom.injective _, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective y
  refine ⟨PowerSeries.constantCoeff x, ?_⟩
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal,
    mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, map_sub, PowerSeries.constantCoeff_C,
    sub_self]
  exact not_isUnit_zero

theorem UpperTheory.V.Pa.Det.resExt :
    ∀ (l : ℕ) [Fact l.Prime] {K : Type} [Field K] [Finite K] [CharP K l] (d D : ℕ), Nat.card K = l ^ d → d ∣ D → D ≠ 0 → ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A') (_ : IsEqDVR l A') (j : PowerSeries K →+* A'), Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧ Nat.card (ResidueField A') = l ^ D ∧ Irreducible (j PowerSeries.X) := by
  intro l _ K _ _ _ d D hK hdD hD
  have hd : d ≠ 0 := by
    rintro rfl
    exact hD (zero_dvd_iff.mp hdD)
  letI : Algebra (ZMod l) K := ZMod.algebra K l
  let e := GaloisField.algEquivGaloisField l d hK
  obtain ⟨g⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod l)
    (K := GaloisField l d) (L := GaloisField l D)
    (by rw [GaloisField.finrank l hd, GaloisField.finrank l hD]; exact hdD)
  let φ : K →+* GaloisField l D := (g.comp e.toAlgHom).toRingHom
  have hcc : ∀ ψ : PowerSeries K, PowerSeries.constantCoeff (PowerSeries.map φ ψ) =
      φ (PowerSeries.constantCoeff ψ) := by
    intro ψ
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  haveI : CharP (PowerSeries (GaloisField l D)) l :=
    charP_of_injective_ringHom (PowerSeries.C (R := GaloisField l D)).injective l
  haveI : UpperTheory.V.Pa.IsEqDVR l (PowerSeries (GaloisField l D)) :=
    ⟨by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance,
      Finite.of_surjective _ (bijective_residue_comp_powerSeries_C (GaloisField l D)).2, inferInstance⟩
  refine ⟨PowerSeries (GaloisField l D), inferInstance, inferInstance, inferInstance, inferInstance,
    PowerSeries.map φ, PowerSeries.map_injective _ φ.injective, ⟨fun ψ hψ => ?_⟩,
    map_finite φ, ?_, ?_⟩
  · rw [PowerSeries.isUnit_iff_constantCoeff, hcc, isUnit_iff_ne_zero,
      map_ne_zero_iff _ φ.injective] at hψ
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    exact hψ
  · rw [← Nat.card_congr (Equiv.ofBijective _ (bijective_residue_comp_powerSeries_C (GaloisField l D))),
      GaloisField.card l D hD]
  · rw [PowerSeries.map_X]
    exact PowerSeries.X_irreducible
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem exists_factor {F A M : Type} [Field F] [AddCommGroup A] [Module F A] [AddCommGroup M] [Module F M]
    (T S : A →ₗ[F] M) (h : LinearMap.ker T ≤ LinearMap.ker S) : ∃ d : M →ₗ[F] M, ∀ c, d (T c) = S c := by
  let S' : LinearMap.range T →ₗ[F] M :=
    ((LinearMap.ker T).liftQ S h).comp T.quotKerEquivRange.symm.toLinearMap
  obtain ⟨d, hd⟩ := LinearMap.exists_extend S'
  refine ⟨d, fun c => ?_⟩
  have h1 : d (T c) = S' ⟨T c, LinearMap.mem_range_self T c⟩ := by
    rw [← hd]
    rfl
  have h2 : T.quotKerEquivRange.symm ⟨T c, LinearMap.mem_range_self T c⟩ = Submodule.Quotient.mk c := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [LinearMap.quotKerEquivRange_apply_mk]
  rw [h1]
  simp only [S', LinearMap.comp_apply, LinearEquiv.coe_coe, h2, Submodule.liftQ_apply]

theorem UpperTheory.V.Pa.Det.der :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (z : G → Matrix (Fin n) (Fin n) F), TwCoc (fun _ => 1) D.r D.G' z → (∀ i j, D.KillsRel z i j) → ∃ Y, ∀ g ∈ D.G', z g = dTw (fun _ => 1) D.r Y g := by
  intro F G _ _ n D z hz hk
  let A := Finsupp.supported F F (D.G' : Set G)
  let T : A →ₗ[F] Matrix (Fin n) (Fin n) F :=
    (Finsupp.linearCombination F (fun g => D.r g)).comp A.subtype
  let S : A →ₗ[F] Matrix (Fin n) (Fin n) F :=
    (Finsupp.linearCombination F (fun g => z g * D.r g)).comp A.subtype
  have hTS : LinearMap.ker T ≤ LinearMap.ker S := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    ext i j
    have hsupp : ∀ g ∈ (c : G →₀ F).support, g ∈ D.G' := fun g hg =>
      (Finsupp.mem_supported F _).1 c.2 hg
    have := hk i j (c : G →₀ F) hsupp (by simpa [T, Finsupp.linearCombination_apply] using hc)
    simpa [S, Finsupp.linearCombination_apply] using this
  obtain ⟨d, hd⟩ := exists_factor T S hTS
  have hdr : ∀ g ∈ D.G', d (D.r g) = z g * D.r g := by
    intro g hg
    have := hd ⟨Finsupp.single g 1, Finsupp.single_mem_supported F 1 hg⟩
    simpa [T, S] using this
  have hr1 : ∀ g, D.r g⁻¹ * D.r g = 1 := fun g => by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hgen : ∀ g ∈ D.G', ∀ h ∈ D.G',
      d (D.r g * D.r h) = d (D.r g) * D.r h + D.r g * d (D.r h) := by
    intro g hg h hh
    rw [← D.r.map_mul, hdr _ (D.G'.mul_mem hg hh), hdr g hg, hdr h hh, hz g hg h hh, D.r.map_mul]
    simp only [one_smul, Matrix.add_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (D.r g⁻¹) (D.r g) (D.r h), hr1, Matrix.one_mul]
  have hder : ∀ x ∈ Ev F F n D.a, ∀ y ∈ Ev F F n D.a, d (x * y) = d x * y + x * d y := by
    intro x hx y hy
    rw [← D.span] at hx hy
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨g, hg, rfl⟩ := hx'
      induction hy using Submodule.span_induction with
      | mem y hy' =>
        obtain ⟨h, hh, rfl⟩ := hy'
        exact hgen g hg h hh
      | zero => simp
      | add y1 y2 _ _ h1 h2 =>
        simp only [Matrix.mul_add, map_add (f := _), h1, h2]
        abel
      | smul a y _ h1 =>
        simp only [Matrix.mul_smul, map_smul, h1, smul_add]
    | zero => simp
    | add x1 x2 _ _ h1 h2 =>
      simp only [Matrix.add_mul, map_add (f := _), h1, h2]
      abel
    | smul a x _ h1 =>
      simp only [Matrix.smul_mul, map_smul, h1, smul_add]
  obtain ⟨Y, hY⟩ := Det.derEv d hder
  refine ⟨-Y, fun g hg => ?_⟩
  have h1 := hY (D.r g) (D.ev g)
  rw [hdr g hg] at h1
  have h2 : z g = (Y * D.r g - D.r g * Y) * D.r g⁻¹ := by
    rw [← h1, Matrix.mul_assoc, ← D.r.map_mul, mul_inv_cancel, map_one, Matrix.mul_one]
  rw [h2]
  simp only [dTw, one_smul, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  rw [← D.r.map_mul, mul_inv_cancel, map_one, Matrix.mul_one]
  abel
end
