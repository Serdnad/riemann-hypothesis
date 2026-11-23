module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.TrivSqZeroExt
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem entry_eq {A : Type} [CommRing A] {n : ℕ} (X : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    X i j = (Matrix.single j i (1 : A) * X).trace := by
  rw [Matrix.trace_single_mul, one_smul]

theorem UpperTheory.V.Ws.Eb.trPlus :
    ∀ {A G : Type} [CommRing A] [Group G] {n : ℕ} (ρ : G →* GL (Fin n) A), Full ρ →
        (∀ z : MonoidAlgebra A G, (∀ h : G, (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single h 1 * z) = 0) → W.GDet.repAlg (W.mat ρ) A z = 0) ∧
        ∀ [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace G] [IsTopologicalGroup G], (Continuous fun g => (W.mat ρ g).trace) → Continuous ρ := by
  intro A G _ _ n ρ hF
  have hs : ∀ h : G, W.GDet.repAlg (W.mat ρ) A (MonoidAlgebra.single h 1) = W.mat ρ h := by
    intro h
    simp [W.GDet.repAlg]
  have hsp : ∀ X : Matrix (Fin n) (Fin n) A, X ∈ Submodule.span A (Set.range (W.mat ρ)) := by
    intro X
    unfold Full at hF
    rw [hF]
    exact Submodule.mem_top
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      ext i j
      exact i.elim0
    have hsingle : ∀ (B : Type) [CommRing B] [Algebra A B] (g : G) (r : B),
        W.GDet.repAlg (W.mat ρ) B (MonoidAlgebra.single g r) =
          r • (W.mat ρ g).map (algebraMap A B) := by
      intro B _ _ g r
      unfold W.GDet.repAlg
      rw [MonoidAlgebra.lift_single]
      rfl
    have hmap : ∀ y : MonoidAlgebra A G,
        W.GDet.repAlg (W.mat ρ) A[X] (MonoidAlgebra.mapRingHom G (algebraMap A A[X]) y) =
          (W.GDet.repAlg (W.mat ρ) A y).map (algebraMap A A[X]) := by
      intro y
      induction y using MonoidAlgebra.induction_on with
      | of g => simp [MonoidAlgebra.of_apply, hsingle]
      | add x y hx hy =>
        rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
        ext i j
        simp
      | smul r x hx =>
        have hr : r • x = MonoidAlgebra.single 1 r * x := by
          rw [Algebra.smul_def]
          rfl
        have hm : MonoidAlgebra.mapRingHom G (algebraMap A A[X]) (MonoidAlgebra.single 1 r)
            = MonoidAlgebra.single 1 (algebraMap A A[X] r) := by
          ext g
          simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]
        rw [hr, map_mul, map_mul, map_mul, hx, Matrix.map_mul, hm, hsingle, hsingle, map_one]
        congr 1
        ext i j
        by_cases h : i = j <;> simp [Matrix.one_apply, h]
    have htr : ∀ y : MonoidAlgebra A G,
        (W.GDet.ofRep (W.mat ρ)).tr y = (W.GDet.repAlg (W.mat ρ) A y).trace := by
      intro y
      have hchi : (W.GDet.ofRep (W.mat ρ)).chi y = (W.GDet.repAlg (W.mat ρ) A y).charpoly := by
        unfold W.GDet.chi
        change (W.GDet.repAlg (W.mat ρ) A[X] _).det = _
        rw [← Polynomial.algebraMap_eq, map_sub, hsingle, hmap, map_one]
        rw [Matrix.charpoly]
        congr 1
        ext i j
        by_cases h : i = j <;> simp [Matrix.charmatrix_apply, Matrix.one_apply, h]
      haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      unfold W.GDet.tr W.GDet.lam
      rw [hchi, Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
      ring
    have key : ∀ X, (X * W.GDet.repAlg (W.mat ρ) A z).trace = 0 := by
      intro X
      induction hsp X using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        rw [← hs h, ← map_mul, ← htr]
        exact hz h
      | zero => simp
      | add x y _ _ hx hy => rw [add_mul, Matrix.trace_add, hx, hy, add_zero]
      | smul a x _ hx => rw [Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
    ext i j
    exact (entry_eq _ i j).trans (key _)
  · intro _ _ _ _ hc
    have key : ∀ X, Continuous fun g => (X * W.mat ρ g).trace := by
      intro X
      induction hsp X using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        simp_rw [← map_mul]
        exact hc.comp (continuous_const_mul h)
      | zero => simpa using continuous_const
      | add x y _ _ hx hy =>
        simp_rw [add_mul, Matrix.trace_add]
        exact hx.add hy
      | smul a x _ hx =>
        simp_rw [Matrix.smul_mul, Matrix.trace_smul]
        exact hx.const_smul a
    have hm : Continuous fun g => W.mat ρ g := by
      apply continuous_matrix
      intro i j
      exact (key (Matrix.single j i 1)).congr (fun g => (entry_eq _ i j).symm)
    rw [Units.continuous_iff]
    refine ⟨hm, ?_⟩
    refine (hm.comp continuous_inv).congr fun x => ?_
    show ((ρ x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = _
    rw [map_inv]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem cocExt_mem {l : ℕ} [Fact l.Prime] (F : W.GFrame l) {x : F.Γ} (hx : x ∉ F.η.ker) : x * F.c ∈ F.η.ker := by
  rw [MonoidHom.mem_ker] at hx ⊢
  rw [map_mul, F.η_c]
  rcases Int.units_eq_one_or (F.η x) with h | h
  · exact absurd h hx
  · rw [h]
    rfl

private theorem cocycle_extends_to_conj_group {l : ℕ} [Fact l.Prime] (F : W.GFrame l) {K M : Type} [CommRing K] [AddCommGroup M] [Module K M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] (R : Representation K F.Γ M) (y : F.G₀ → M) (w : M)
    (hy : Continuous y) (hyc : ∀ g h : F.G₀, y (g * h) = y g + R g (y h))
    (hw : Continuous fun g : F.G₀ => R g w) (hcw : R F.c w = -w)
    (hrel : ∀ g : F.G₀, y (F.conj g) = R F.c (y g) + (w - R (F.conj g) w)) :
    ∃ z : F.Γ → M, Continuous z ∧ (∀ g h, z (g * h) = z g + R g (z h)) ∧ ∀ g : F.G₀, z g = y g := by
  have hcc : F.c * F.c = 1 := F.c_sq
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hcc
  have hc2 : ∀ x : F.Γ, x * F.c * F.c = x := fun x => by rw [mul_assoc, hcc, mul_one]
  have I1 : ∀ g h : F.Γ, g * F.c * (F.c * h * F.c) = g * h * F.c := fun g h => by
    simp only [mul_assoc]
    rw [← mul_assoc F.c F.c, hcc, one_mul]
  have I2 : ∀ g h : F.Γ, g * F.c * (F.c * (h * F.c) * F.c) = g * h := fun g h => by
    simp only [mul_assoc]
    rw [hcc, mul_one, ← mul_assoc F.c F.c, hcc, one_mul]
  have hker : IsOpen (F.η.ker : Set F.Γ) := F.η_open
  have hkerc : IsOpen (F.η.ker : Set F.Γ)ᶜ := (Subgroup.isClosed_of_isOpen _ hker).isOpen_compl
  have Rm : ∀ (a b : F.Γ) (v : M), R (a * b) v = R a (R b v) := fun a b v => by rw [map_mul]; rfl
  have hconj : ∀ k : F.G₀, ((F.conj k : F.G₀) : F.Γ) = F.c * k * F.c := fun k => by
    simp [W.GFrame.conj, hci]
  have hneg : ∀ x : F.Γ, x ∉ F.η.ker → F.η x = -1 := fun x hx => by
    rcases Int.units_eq_one_or (F.η x) with h | h
    · exact absurd (MonoidHom.mem_ker.mpr h) hx
    · exact h
  let z : F.Γ → M := fun x =>
    if hx : x ∈ F.η.ker then y ⟨x, hx⟩ else y ⟨x * F.c, cocExt_mem F hx⟩ + R (x * F.c) w
  have zin : ∀ x (hx : x ∈ F.η.ker), z x = y ⟨x, hx⟩ := fun x hx => dif_pos hx
  have zout : ∀ x (hx : x ∉ F.η.ker), z x = y ⟨x * F.c, cocExt_mem F hx⟩ + R (x * F.c) w :=
    fun x hx => dif_neg hx
  refine ⟨z, ?_, ?_, fun g => zin g g.2⟩
  · rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ F.η.ker
    · apply ContinuousOn.continuousAt _ (hker.mem_nhds hx)
      rw [continuousOn_iff_continuous_restrict]
      have hm : Continuous fun p : (F.η.ker : Set F.Γ) => (⟨p.1, p.2⟩ : F.G₀) :=
        continuous_subtype_val.subtype_mk fun p => p.2
      refine (hy.comp hm).congr fun p => ?_
      exact (zin p.1 p.2).symm
    · apply ContinuousOn.continuousAt _ (hkerc.mem_nhds hx)
      rw [continuousOn_iff_continuous_restrict]
      have hm : Continuous fun p : ((F.η.ker : Set F.Γ)ᶜ : Set F.Γ) => (⟨p.1 * F.c, cocExt_mem F p.2⟩ : F.G₀) :=
        (continuous_subtype_val.mul continuous_const).subtype_mk _
      refine ((hy.comp hm).add (hw.comp hm)).congr fun p => ?_
      exact (zout p.1 p.2).symm
  · intro g h
    by_cases hg : g ∈ F.η.ker <;> by_cases hh : h ∈ F.η.ker
    · rw [zin _ (mul_mem hg hh), zin _ hg, zin _ hh]
      exact hyc ⟨g, hg⟩ ⟨h, hh⟩
    · have hgh : g * h ∉ F.η.ker := fun H => hh (by simpa using mul_mem (inv_mem hg) H)
      rw [zout _ hgh, zin _ hg, zout _ hh]
      have e : (⟨g * h * F.c, cocExt_mem F hgh⟩ : F.G₀) = ⟨g, hg⟩ * ⟨h * F.c, cocExt_mem F hh⟩ :=
        Subtype.ext (mul_assoc _ _ _)
      rw [e, hyc, map_add (f := _), ← Rm, ← mul_assoc]
      exact add_assoc _ _ _
    · have hgh : g * h ∉ F.η.ker := fun H => hg (by simpa using mul_mem H (inv_mem hh))
      rw [zout _ hgh, zout _ hg, zin _ hh]
      have e : (⟨g * h * F.c, cocExt_mem F hgh⟩ : F.G₀) = ⟨g * F.c, cocExt_mem F hg⟩ * F.conj ⟨h, hh⟩ := by
        apply Subtype.ext
        show g * h * F.c = g * F.c * ((F.conj ⟨h, hh⟩ : F.G₀) : F.Γ)
        rw [hconj]
        exact (I1 g h).symm
      rw [e, hyc, hrel, map_add (f := _), map_sub]
      have e1 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R F.c (y ⟨h, hh⟩)) = R g (y ⟨h, hh⟩) := by
        rw [← Rm]
        show R (g * F.c * F.c) _ = _
        rw [hc2]
      have e2 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R (↑(F.conj ⟨h, hh⟩)) w) = R (g * h * F.c) w := by
        rw [← Rm, hconj]
        show R (g * F.c * (F.c * h * F.c)) w = _
        rw [I1]
      rw [e1, e2]
      show y _ + (R g _ + (R (g * F.c) w - R (g * h * F.c) w)) + R (g * h * F.c) w = y _ + R (g * F.c) w + R g _
      abel
    · have hgh : g * h ∈ F.η.ker := by
        rw [MonoidHom.mem_ker, map_mul, hneg g hg, hneg h hh]
        decide
      rw [zin _ hgh, zout _ hg, zout _ hh]
      have e : (⟨g * h, hgh⟩ : F.G₀) = ⟨g * F.c, cocExt_mem F hg⟩ * F.conj ⟨h * F.c, cocExt_mem F hh⟩ := by
        apply Subtype.ext
        show g * h = g * F.c * ((F.conj ⟨h * F.c, cocExt_mem F hh⟩ : F.G₀) : F.Γ)
        rw [hconj]
        exact (I2 g h).symm
      rw [e, hyc, hrel, map_add (f := _), map_sub, map_add (f := _)]
      have e1 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R F.c (y ⟨h * F.c, cocExt_mem F hh⟩)) =
          R g (y ⟨h * F.c, cocExt_mem F hh⟩) := by
        rw [← Rm]
        show R (g * F.c * F.c) _ = _
        rw [hc2]
      have e2 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R (↑(F.conj ⟨h * F.c, cocExt_mem F hh⟩)) w) =
          -R g (R (h * F.c) w) := by
        rw [← Rm, hconj]
        show R (g * F.c * (F.c * (h * F.c) * F.c)) w = _
        rw [I2, ← Rm, ← mul_assoc, Rm (g * h) F.c, hcw, map_neg, neg_neg]
      rw [e1, e2]
      show y _ + (R g _ + (R (g * F.c) w - -R g (R (h * F.c) w))) = y _ + R (g * F.c) w + (R g _ + R g (R (h * F.c) w))
      abel

theorem UpperTheory.V.Ws.Eb.cocExt :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) {K : Type} [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ} (ρ : F.G₀ →* GL (Fin n) K) (P : GL (Fin n) K) (R : Representation K F.Γ (Matrix (Fin n) (Fin n) K)), Full ρ → Continuous ρ → IsAdExt F ρ P R →
        ∀ y ∈ Z1 (Loc.adGL ρ), ∀ Z, (∀ g, y (F.conj g) = R F.c (y g) + (R (F.conj g) Z - Z)) → ∃ z ∈ Z1 R, ∀ g : F.G₀, z g = y g := by
  intro l _ F K _ _ _ _ n ρ P R hF hρ hA y hy Z hZ
  obtain ⟨hy0, hycoc⟩ := hy
  have hcc : F.c * F.c = 1 := F.c_sq
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hcc
  have Rm : ∀ (a b : F.Γ) (v : Matrix (Fin n) (Fin n) K), R (a * b) v = R a (R b v) :=
    fun a b v => by rw [map_mul]; rfl
  have Rcc : ∀ v, R F.c (R F.c v) = v := fun v => by rw [← Rm, hcc, map_one]; rfl
  have hconj : ∀ k : F.G₀, ((F.conj k : F.G₀) : F.Γ) = F.c * k * F.c := fun k => by
    simp [W.GFrame.conj, hci]
  have cc : ∀ g : F.G₀, F.conj (F.conj g) = g := fun g => by
    apply Subtype.ext
    rw [hconj, hconj]
    simp only [← mul_assoc, hcc, one_mul]
    rw [mul_assoc, hcc, mul_one]
  have hyc : ∀ g h : F.G₀, y (g * h) = y g + R g (y h) := fun g h => by
    rw [hycoc g h, hA.ad]
  have hinv : ∀ g : F.G₀, R g (Z + R F.c Z) = Z + R F.c Z := by
    intro g
    have e2 := hZ (F.conj g)
    rw [cc, hZ g, map_add (f := _), Rcc, map_sub, ← Rm, hconj] at e2
    have ec : F.c * (F.c * (g : F.Γ) * F.c) = g * F.c := by
      rw [← mul_assoc, ← mul_assoc, hcc, one_mul]
    rw [ec, Rm] at e2
    rw [map_add (f := _), ← sub_eq_zero, ← neg_eq_zero]
    rw [← sub_eq_zero] at e2
    rw [← e2]
    abel
  set w : Matrix (Fin n) (Fin n) K := (2 : K)⁻¹ • (R F.c Z - Z) with hwdef
  have hcw : R F.c w = -w := by
    rw [hwdef, map_smul, map_sub, Rcc, ← smul_neg, neg_sub]
  have hrel : ∀ g : F.G₀, y (F.conj g) = R F.c (y g) + (w - R (F.conj g) w) := by
    intro g
    rw [hZ g]
    congr 1
    have hi := hinv (F.conj g)
    rw [map_add (f := _)] at hi
    rw [hwdef, map_smul, map_sub, ← smul_sub]
    have hb : R (F.conj g) (R F.c Z) = Z + R F.c Z - R (F.conj g) Z := by
      rw [← hi]
      abel
    rw [hb]
    have e : R F.c Z - Z - (Z + R F.c Z - R (↑(F.conj g)) Z - R (↑(F.conj g)) Z) =
        (2 : K) • (R (↑(F.conj g)) Z - Z) := by
      rw [two_smul]
      abel
    rw [e, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  have hw : Continuous fun g : F.G₀ => R g w := by
    have e : (fun g : F.G₀ => R g w) =
        fun g => (↑(ρ g) : Matrix (Fin n) (Fin n) K) * w * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K) :=
      funext fun g => by rw [hA.ad]; rfl
    rw [e]
    exact ((Units.continuous_val.comp hρ).matrix_mul continuous_const).matrix_mul (Units.continuous_coe_inv.comp hρ)
  obtain ⟨z, hz, hzc, hzy⟩ := cocycle_extends_to_conj_group F R y w hy0 hyc hw hcw hrel
  exact ⟨z, ⟨hz, hzc⟩, hzy⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private def ebS {K : Type} [CommRing K] {n : ℕ} (X : Matrix (Fin n) (Fin n) (DualNumber K)) :
    Matrix (Fin n) (Fin n) K := Matrix.of fun i j => (X i j).snd

private theorem ebS_mul {K : Type} [CommRing K] {n : ℕ} (X Y : Matrix (Fin n) (Fin n) (DualNumber K)) :
    ebS (X * Y) = X.map (dF K) * ebS Y + ebS X * Y.map (dF K) := by
  ext i j
  simp only [ebS, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.add_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [dF, smul_eq_mul, MulOpposite.smul_eq_mul_unop, mul_comm]

theorem UpperTheory.V.Ws.Eb.tanOf :
    ∀ {K G : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ} (ρ' : G →* GL (Fin n) (DualNumber K)), Continuous ρ' →
        Continuous (W.pushRep (dF K) ρ') ∧ ∃ y ∈ Z1 (Loc.adGL (W.pushRep (dF K) ρ')), IsTan (W.pushRep (dF K) ρ') y ρ' := by
  intro K G _ _ _ _ _ _ n ρ' hρ'
  set ρ := W.pushRep (dF K) ρ' with hρ
  have hdF : Continuous (dF K) := TrivSqZeroExt.continuous_fst
  have hv : Continuous fun g => (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) :=
    Units.continuous_val.comp hρ'
  have hi : Continuous fun g => (↑((ρ' g)⁻¹) : Matrix (Fin n) (Fin n) (DualNumber K)) :=
    Units.continuous_coe_inv.comp hρ'
  have hc : Continuous ρ := by
    rw [Units.continuous_iff]
    exact ⟨hv.matrix_map hdF, hi.matrix_map hdF⟩
  have hci : Continuous fun g => (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K) :=
    Units.continuous_coe_inv.comp hc
  have e : ∀ g, (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)).map (dF K) = (↑(ρ g) : Matrix (Fin n) (Fin n) K) :=
    fun g => rfl
  have hS : Continuous fun g => ebS (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) :=
    continuous_matrix fun i j => TrivSqZeroExt.continuous_snd.comp (hv.matrix_elem i j)
  refine ⟨hc, fun g => ebS (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K),
    ⟨hS.matrix_mul hci, ?_⟩, ?_⟩
  · intro g h
    show ebS (↑(ρ' (g * h)) : Matrix (Fin n) (Fin n) (DualNumber K)) * (↑((ρ (g * h))⁻¹) : Matrix (Fin n) (Fin n) K) =
      ebS (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K) +
        (↑(ρ g) : Matrix (Fin n) (Fin n) K) * (ebS (↑(ρ' h) : Matrix (Fin n) (Fin n) (DualNumber K)) *
          (↑((ρ h)⁻¹) : Matrix (Fin n) (Fin n) K)) * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K)
    rw [map_mul, map_mul, Units.val_mul, ebS_mul, e, e, _root_.mul_inv_rev, Units.val_mul, add_mul]
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
    exact add_comm _ _
  · intro g i j
    show _ = (_, (ebS (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K) *
      (↑(ρ g) : Matrix (Fin n) (Fin n) K)) i j)
    rw [Units.inv_mul_cancel_right]
    rfl
end
