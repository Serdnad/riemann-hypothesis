module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle638
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConnPhiExtensionGeneratorEqZeta
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle642
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle622
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle643
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle644
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.SliceLdiv

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem frobSlice_zero (l i : ℕ) : frobSlice l i (0 : K⟦X⟧) = 0 := by
  ext n; simp [coeff_frobSlice]

theorem frobSlice_sum {β : Type} (l i : ℕ) (s : Finset β) (g : β → K⟦X⟧) :
    frobSlice l i (∑ b ∈ s, g b) = ∑ b ∈ s, frobSlice l i (g b) := by
  ext n; simp [coeff_frobSlice, map_sum]

theorem frobSlice_mul_frob {l : ℕ} [Fact l.Prime] {i : ℕ} (hi : i < l) (z f : K⟦X⟧) :
    frobSlice l i (z * frob K l f) = frobSlice l i z * f := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  ext n
  rw [coeff_frobSlice, coeff_mul, coeff_mul]
  have hval : ∀ p q : ℕ, coeff (l * p + i) z * coeff q f =
      coeff (l * p + i) z * coeff (l * q) (frob K l f) := by
    intro p q
    rw [coeff_frob, if_pos (dvd_mul_right l q), Nat.mul_div_cancel_left q hl]
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => (l * p.1 + i, l * p.2)) ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ hpq -
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hpq ⊢
    rw [← hpq, mul_add]; ring
  · rintro ⟨p, q⟩ - - ⟨p', q'⟩ - - h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : p = p' := Nat.eq_of_mul_eq_mul_left hl (by omega)
    have h2' : q = q' := Nat.eq_of_mul_eq_mul_left hl h2
    rw [h1', h2']
  · rintro ⟨a, b⟩ hab hne
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    rw [coeff_frob] at hne
    split_ifs at hne with hdvd
    · obtain ⟨q, rfl⟩ := hdvd
      have hq : q ≤ n := by
        by_contra hc
        have : l * (n + 1) ≤ l * q := Nat.mul_le_mul_left l (by omega)
        rw [mul_add, mul_one] at this
        omega
      have key : l * (n - q) + l * q = l * n := by rw [← mul_add, Nat.sub_add_cancel hq]
      have ha : a = l * (n - q) + i := by omega
      subst ha
      rw [Nat.mul_div_cancel_left q hl] at hne
      exact ⟨(n - q, q), by simp only [Finset.HasAntidiagonal.mem_antidiagonal]; omega,
        by simp only [coeff_frobSlice]; exact hne, rfl⟩
    · exact absurd (mul_zero _) hne
  · rintro ⟨p, q⟩ - -
    simp only [coeff_frobSlice]
    exact hval p q

theorem bdd_frobSlice (l i : ℕ) {z : K⟦X⟧} (hz : ∃ c : ℝ, ∀ n, ‖coeff n z‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (frobSlice l i z)‖ ≤ c := by
  obtain ⟨c, hc⟩ := hz
  exact ⟨c, fun n => by rw [coeff_frobSlice]; exact hc _⟩

theorem bdd_of_mem_A {f : K⟦X⟧} (hf : f ∈ A O K) : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c := ⟨1, hf⟩

theorem bdd_zero : ∃ c : ℝ, ∀ n, ‖coeff n (0 : K⟦X⟧)‖ ≤ c := ⟨0, fun n => by simp⟩

theorem bdd_sum {β : Type} (s : Finset β) (g : β → K⟦X⟧) (hg : ∀ b ∈ s, ∃ c : ℝ, ∀ n, ‖coeff n (g b)‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (∑ b ∈ s, g b)‖ ≤ c :=
  Finset.sum_induction g (fun f : K⟦X⟧ => ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c)
    (fun _ _ => Hom.bdd_add) bdd_zero hg

theorem bdd_matMul {μ ν ρ : Type} [Fintype ν] {M : Matrix μ ν K⟦X⟧} {N : Matrix ν ρ K⟦X⟧}
    (hM : ∀ i j, ∃ c : ℝ, ∀ n, ‖coeff n (M i j)‖ ≤ c) (hN : ∀ i j, ∃ c : ℝ, ∀ n, ‖coeff n (N i j)‖ ≤ c)
    (i : μ) (j : ρ) : ∃ c : ℝ, ∀ n, ‖coeff n ((M * N) i j)‖ ≤ c := by
  rw [Matrix.mul_apply]
  exact bdd_sum _ _ fun k _ => Hom.bdd_mul (hM i k) (hN k j)

theorem bdd_unif {μ ν : Type} [Finite μ] [Finite ν] {M : Matrix μ ν K⟦X⟧}
    (h : ∀ i j, ∃ c : ℝ, ∀ n, ‖coeff n (M i j)‖ ≤ c) : ∃ c : ℝ, ∀ i j n, ‖coeff n (M i j)‖ ≤ c := by
  choose c hc using h
  obtain ⟨C, hC⟩ := Finite.bddAbove_range (fun p : μ × ν => c p.1 p.2)
  exact ⟨C, fun i j n => (hc i j n).trans (hC ⟨(i, j), rfl⟩)⟩

theorem exists_pow_E_mul_mem (l e : ℕ) {β : Type} [Finite β] (g : β → K⟦X⟧)
    (hg : ∀ b, g b ∈ invE l e (A O K)) : ∃ N : ℕ, ∀ b, E K l e ^ N * g b ∈ A O K := by
  have := Fintype.ofFinite β
  choose n hn using fun b => (mem_away.1 (hg b))
  refine ⟨Finset.univ.sup n, fun b => ?_⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ b))
  rw [hc, pow_add, mul_assoc]
  exact mul_mem (pow_mem (E_mem l e _) c) (by simpa using hn b)

theorem frobSlice_mem_ldivSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.ldivSet τ, ∀ i < l, frobSlice l i (E K l e ^ M * h) ∈ F.ldivSet (τ - 1) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  obtain ⟨N₁, hN₁⟩ := exists_pow_E_mul_mem (O := O) l e
    (fun p : ZMod a × ι × ι => P.mxInv p.1 p.2.1 p.2.2) (fun p => P.mxInv_mem _ _ _)
  obtain ⟨N₂, hN₂⟩ := exists_pow_E_mul_mem (O := O) l e
    (fun p : ZMod a × κ × κ => Q.mx p.1 p.2.1 p.2.2) (fun p => Q.mx_mem _ _ _)
  refine ⟨N₁ + N₂, fun τ h hh i hi => ?_⟩
  obtain ⟨hhb, Y, ⟨cY, hcY⟩, hY⟩ := hh
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix ι κ K⟦X⟧,
      Z = (E K l e ^ N₁ • P.mxInv τ) * Y * (E K l e ^ N₂ • Q.mx τ) := ⟨_, rfl⟩
  have h1 : Y * Q.mx τ * (F.mat (τ - 1)).map (frob K l) = h • P.mx τ := by
    rw [Matrix.mul_assoc, ← F.comm, ← Matrix.mul_assoc, hY, Matrix.smul_mul, Matrix.one_mul]
  have hZF : Z * (F.mat (τ - 1)).map (frob K l) =
      (E K l e ^ (N₁ + N₂) * h) • (1 : Matrix ι ι K⟦X⟧) := by
    have : Z * (F.mat (τ - 1)).map (frob K l) =
        E K l e ^ N₁ • E K l e ^ N₂ • (P.mxInv τ * (Y * Q.mx τ * (F.mat (τ - 1)).map (frob K l))) := by
      simp only [hZ, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
      exact smul_comm _ _ _
    rw [this, h1, Matrix.mul_smul, P.mxInv_mul_mx]
    simp only [smul_smul, pow_add, mul_assoc]
  have hPb : ∀ r k, ∃ c : ℝ, ∀ n, ‖coeff n ((E K l e ^ N₁ • P.mxInv τ) r k)‖ ≤ c := fun r k =>
    bdd_of_mem_A (O := O) (by rw [Matrix.smul_apply, smul_eq_mul]; exact hN₁ (τ, r, k))
  have hQb : ∀ k c, ∃ c' : ℝ, ∀ n, ‖coeff n ((E K l e ^ N₂ • Q.mx τ) k c)‖ ≤ c' := fun k c =>
    bdd_of_mem_A (O := O) (by rw [Matrix.smul_apply, smul_eq_mul]; exact hN₂ (τ, k, c))
  have hYb : ∀ r k, ∃ c : ℝ, ∀ n, ‖coeff n (Y r k)‖ ≤ c := fun r k => ⟨cY, hcY r k⟩
  have hZb : ∀ r c, ∃ c' : ℝ, ∀ n, ‖coeff n (Z r c)‖ ≤ c' := fun r c => by
    rw [hZ]; exact bdd_matMul (bdd_matMul hPb hYb) hQb r c
  refine ⟨bdd_frobSlice l i (Hom.bdd_mul (bdd_of_mem_A (O := O) (pow_mem (E_mem l e (A O K)) _)) hhb),
    Z.map (frobSlice l i), bdd_unif fun r c => ?_, ?_⟩
  · rw [Matrix.map_apply]; exact bdd_frobSlice l i (hZb r c)
  · ext r c
    have hrc := congrFun (congrFun hZF r) c
    rw [Matrix.mul_apply] at hrc
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply] at hrc ⊢
    simp_rw [← frobSlice_mul_frob hi]
    rw [← frobSlice_sum, hrc, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      smul_eq_mul]
    split_ifs
    · rw [mul_one, mul_one]
    · rw [mul_zero, mul_zero, frobSlice_zero]

end GlobalTheory.BK.SliceLdiv
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKBasis



theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∃ b : ι → E.M (ϖ.prism a), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) ∧ ∀ x : E.M (ϖ.prism a), ∃ (N : ℕ) (c : ι → Fin N → O) (s : ι → Fin N → (ϖ.prism a).A), x = ∑ j, ∑ q, s j q • (oE (c j q)).u (ϖ.prism a) (b j) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  letI := zlLat T
  intro E jA H him oE hoE
  obtain ⟨J, hJ⟩ : ∃ J : E.M (ϖ.prism a) →+ TW (OW l O) T,
      ∀ x, J x = kappa T (jA (E.tr (ϖ.toAinf a) x)) :=
    ⟨(kappa T).comp (jA.toAddMonoidHom.comp (E.tr (ϖ.toAinf a)).toAddMonoidHom), fun _ => rfl⟩
  have h1 : ∀ y : TW (OW l O) T, (∃ x, y = J x) ↔
      ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) := fun y => by
    simp only [hJ]
    exact him y
  obtain ⟨c, hc, hcJ, hs⟩ := GlobalTheory.BKCoord.exists_coord I J h1
  have hi : Function.Injective J := by
    have := E.proj (ainfObj (ϖ.field a))
    have := E.proj (ϖ.prism a)
    intro x y h
    rw [hJ, hJ] at h
    exact GlobalTheory.BKCoord.semiBC_injective (E.tr_bc (ϖ.toAinf a)) (GlobalTheory.BKCoord.ev_injective ϖ)
      (GlobalTheory.BKCoord.semiBC_injective H.bc inclW_injective ((kappa_bijective T).1 h))
  have hci : Function.Injective c := fun x y hxy => hi (by rw [hcJ, hcJ]; simp only [hxy])
  have hsm : ∀ (w : (ϖ.prism a).A) (x : E.M (ϖ.prism a)),
      c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i := fun w x => by
    refine GlobalTheory.BKCoord.eq_of_j_eq_toAc I w ⟨_, mem_ME_of_mem_M (hc x)⟩ ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_
    have h3 := congrArg jA ((E.tr (ϖ.toAinf a)).map_smulₛₗ w x)
    have h4 := congrArg (kappa T) (h3.trans (jA.map_smulₛₗ _ _))
    have h5 := h4.trans (GlobalTheory.BKCoord.kappa_smul T _ _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h5
  have hom : ∀ (o : O) (x : E.M (ϖ.prism a)),
      c ((oE o).u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i := fun o x => by
    refine GlobalTheory.BKCoord.eq_of_j_eq_const I o ⟨_, mem_ME_of_mem_M (hc x)⟩ ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_
    have h3 := (congrArg jA ((oE o).u_tr (ϖ.toAinf a) x)).symm.trans (hoE o _)
    have hk : ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T,
        kappa T ((OfCrystal.mulZ T o).lTensor (WCb l) y) = o • kappa T y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero, smul_zero]
      | tmul v z => exact tmul_smul o ((1 : O) ⊗ₜ[ℤ_[l]] v : OW l O) z
      | add y y' hy hy' => simp only [map_add (f := _), smul_add, hy, hy']
    have h4 := (congrArg (kappa T) h3).trans (hk _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h4
  have hbas : ∀ j, (bas j : Vec K a ι) ∈ P.M := fun j => mem_tot.2 fun τ i => by
    change (Pi.single j (1 : K⟦X⟧) : ι → K⟦X⟧) i ∈ A O K
    by_cases h : i = j
    · subst h
      rw [Pi.single_eq_same]
      exact one_mem _
    · rw [Pi.single_eq_of_ne h]
      exact zero_mem _
  choose b hb using fun j => hs _ (hbas j)
  refine ⟨b, fun j => ⟨hbas j, ?_⟩, fun x => ?_⟩
  · rw [← hJ, hcJ]
    have e1 : (⟨c (b j), mem_ME_of_mem_M (hc _)⟩ : ME P) = ⟨bas j, mem_ME_of_mem_M (hbas j)⟩ :=
      Subtype.ext (hb j)
    rw [e1]
  · let o := Module.finBasis ℤ_[l] O
    have hf : ∀ i, ∃ s : Fin (Module.finrank ℤ_[l] O) → (Wq l a)⟦X⟧,
        (fun τ => (⟨c x τ i, mem_tot.1 (hc x) τ i⟩ : A O K)) = ∑ q, o q • toAc t K (s q) :=
      fun i => exists_eq_sum_toAc t K o _
    choose s hs' using hf
    refine ⟨Module.finrank ℤ_[l] O, fun _ q => o q, s, hci ?_⟩

    simp only [map_sum, hsm, hom, hb]
    funext τ i
    have h6 := congrArg (fun f : ZMod a → A O K => (f τ : K⟦X⟧)) (hs' i)
    simp only [Finset.sum_apply, Pi.smul_apply, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h6
    rw [h6]
    simp only [Finset.sum_apply]
    symm
    rw [Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun q _ => ?_
      have h7 := hsm (s i q) ((oE (o q)).u (ϖ.prism a) (b i))
      erw [h7, hom, hb]
      simp only [bas, Pi.single_eq_same, mul_one, Algebra.smul_def, algebraMap_eq_C]
      exact mul_comm _ _
    · intro j _ hj
      refine Finset.sum_eq_zero fun q _ => ?_
      have h7 := hsm (s j q) ((oE (o q)).u (ϖ.prism a) (b j))
      erw [h7, hom, hb]
      simp only [bas, Pi.single_eq_of_ne (Ne.symm hj), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
end GlobalTheory.BKBasis
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysIndep

theorem exists_read {Z O S W R N ι : Type} [CommRing Z] [CommRing O] [CommRing S] [CommRing W] [CommRing R]
    [Algebra Z O] [Algebra Z S] [Algebra Z W] [Algebra O R] [Module.Flat Z O] [AddCommGroup N]
    (ρ : S →ₐ[Z] W) (hρ : Function.Injective ρ) (g : S →+* R)
    (hg : ∀ z, g (algebraMap Z S z) = algebraMap O R (algebraMap Z O z)) (D : N →+ (ι → O ⊗[Z] W))
    (hD : ∀ x i, ∃ z, Algebra.TensorProduct.map (AlgHom.id O O) ρ z = D x i) :
    ∃ V : N →+ (ι → R), (∀ s x x' i, D x' i = ((1 : O) ⊗ₜ[Z] ρ s) * D x i → V x' i = g s * V x i) ∧
      (∀ (c : O) x i, D x i = algebraMap O _ c → V x i = algebraMap O R c) := by
  letI : Algebra Z R := ((algebraMap O R).comp (algebraMap Z O)).toAlgebra
  haveI : IsScalarTower Z O R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g' : S →ₐ[Z] R := { toRingHom := g, commutes' := hg }
  let Ψ : O ⊗[Z] S →ₐ[O] R :=
    Algebra.TensorProduct.lift (Algebra.ofId O R) g' fun _ _ => Commute.all _ _
  have hi : Function.Injective (Algebra.TensorProduct.map (AlgHom.id O O) ρ) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := O) ρ.toLinearMap hρ
  choose C hC using hD
  refine ⟨AddMonoidHom.mk' (fun x i => Ψ (C x i)) fun x y => funext fun i => ?_, fun s x x' i h => ?_,
    fun c x i h => ?_⟩
  · have : C (x + y) i = C x i + C y i := hi (by rw [map_add (f := _), hC, hC, hC, map_add (f := _), Pi.add_apply])
    change Ψ (C (x + y) i) = Ψ (C x i) + Ψ (C y i)
    rw [this, map_add (f := _)]
  · have : C x' i = ((1 : O) ⊗ₜ[Z] s) * C x i := hi (by
      rw [map_mul, hC, hC, h, Algebra.TensorProduct.map_tmul]; rfl)
    change Ψ (C x' i) = g s * Ψ (C x i)
    rw [this, map_mul, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  · have : C x i = algebraMap O _ c := hi (by rw [hC, h, AlgHom.commutes])
    change Ψ (C x i) = _
    rw [this, AlgHom.commutes]

theorem indep_of_coord {Z O S W B R M N ι : Type} [CommRing Z] [CommRing O] [CommRing S] [CommRing W] [CommRing B]
    [CommRing R] [Algebra Z O] [Algebra Z S] [Algebra Z W] [Algebra O R] [Module.Flat Z O] [AddCommGroup M]
    [Module S M] [AddCommGroup N] [Module B N] [Fintype ι] [DecidableEq ι] {f : S →+* B} {u : M →ₛₗ[f] N}
    (hu : SemiBC u) (ρ : S →ₐ[Z] W) (hρ : Function.Injective ρ) (ψ : B →+* R)
    (hψ : ∀ z, ψ (f (algebraMap Z S z)) = algebraMap O R (algebraMap Z O z)) (D : M →+ (ι → O ⊗[Z] W))
    (hD : ∀ x i, ∃ z, Algebra.TensorProduct.map (AlgHom.id O O) ρ z = D x i)
    (hs : ∀ (s : S) x, D (s • x) = ((1 : O) ⊗ₜ[Z] ρ s) • D x) (m : O → ι → M)
    (hm : ∀ o j k, D (m o j) k = o • if k = j then 1 else 0) :
    ∃ lam : N →+ (ι → R), ∀ (Q : Type) [Fintype Q] (c : ι → Q → O) (y : ι → Q → B) (i : ι),
      lam (∑ j, ∑ q, y j q • u (m (c j q) j)) i = ∑ q, c i q • ψ (y i q) := by
  obtain ⟨V, hV1, hV2⟩ := exists_read ρ hρ (ψ.comp f) hψ D hD
  have hVb : ∀ (o : O) j k, V (m o j) k = algebraMap O R (if k = j then o else 0) := fun o j k => by
    refine hV2 _ _ _ ?_
    rw [hm]
    split_ifs
    · exact (Algebra.algebraMap_eq_smul_one o).symm
    · rw [smul_zero, map_zero]
  let V' : M →+ (Unit → ι → R) := AddMonoidHom.mk' (fun x _ => V x)
    fun x y => funext fun _ => map_add V x y
  obtain ⟨lam, hl1, hl2⟩ := CrysExt.exists_ext hu (fun _ : Unit => ψ) V' fun w x _ k =>
    hV1 w x (w • x) k (by rw [hs]; rfl)
  refine ⟨(Pi.evalAddMonoidHom _ ()).comp lam, fun Q _ c y i => ?_⟩
  have h3 : ∀ j q, lam (y j q • u (m (c j q) j)) () i =
      if i = j then c j q • ψ (y j q) else 0 := fun j q => by
    rw [hl1, hl2]
    change _ * V _ i = _
    rw [hVb]
    split_ifs
    · rw [Algebra.smul_def, mul_comm]
    · rw [map_zero, mul_zero]
  change lam _ () i = _

  simp only [map_sum, Finset.sum_apply, h3]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]


variable (a) in
noncomputable def evW (ϖ : PiSys l e) : (Wq l a)⟦X⟧ →ₐ[ℤ_[l]] WCb l where
  toRingHom := (inclW l).comp (ϖ.ev a)
  commutes' z := by
    change inclW l (ϖ.ev a (algebraMap ℤ_[l] (Wq l a)⟦X⟧ z)) = _
    rw [PowerSeries.algebraMap_apply, PiSys.ev_C, AlgHom.commutes]
    exact (inclWA l).commutes z

variable {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι}

theorem exists_toW_eq {m : Vec K a ι} (hm : m ∈ P.M) (i : ι) :
    ∃ z, Algebra.TensorProduct.map (AlgHom.id O O) (evW a ϖ) z = toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩ i := by
  have h1 : toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩ i =
      OfCrystal.iR K t ϖ fun τ => ⟨m τ i, mem_tot.1 hm τ i⟩ :=
    ϖ.iW_of_mem t K fun τ => ⟨m τ i, mem_tot.1 hm τ i⟩
  obtain ⟨s, hs⟩ := exists_eq_sum_toAc t K (Module.Free.chooseBasis ℤ_[l] O)
    (fun τ => ⟨m τ i, mem_tot.1 hm τ i⟩)
  refine ⟨∑ k, Module.Free.chooseBasis ℤ_[l] O k • ((1 : O) ⊗ₜ[ℤ_[l]] s k), ?_⟩

  rw [h1, hs, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul, OfCrystal.iR_toAc]
  rfl

theorem toW_bas (j : ι) (hm : (bas j : Vec K a ι) ∈ P.M) (i : ι) :
    toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩ i = if i = j then 1 else 0 := by
  rw [toW_apply]
  split_ifs with h
  · rw [← map_one (ϖ.iW t K)]
    exact congrArg _ (funext fun τ => Subtype.ext (by simp [bas, h]))
  · rw [← map_zero (ϖ.iW t K)]
    exact congrArg _ (funext fun τ => Subtype.ext (by simp [bas, h]))

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → (∀ i, (oE 1).u (ϖ.prism a) (b i) = b i) ∧ ∀ (P' : Obj l ↥(OL (ϖ.field a))) (f : GlobalTheory.Prism.Hom (ϖ.prism a) P') (Q Q' : Type) [Fintype Q] [Fintype Q'] (c : ι → Q → O) (y : ι → Q → P'.A) (c' : ι → Q' → O) (y' : ι → Q' → P'.A), ∑ i, ∑ q, y i q • (oE (c i q)).u P' (E.tr f (b i)) = ∑ i, ∑ q, y' i q • (oE (c' i q)).u P' (E.tr f (b i)) → ∀ (R : Type) [CommRing R] [Algebra O R] (ψ : P'.A →+* R), (∀ z : ℤ_[l], ψ (f.f (algebraMap ℤ_[l] (Wq l a)⟦X⟧ z)) = algebraMap O R (algebraMap ℤ_[l] O z)) → ∀ i, ∑ q, c i q • ψ (y i q) = ∑ q, c' i q • ψ (y' i q) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  letI := zlLat T
  intro E jA H him oE hoE b hb
  have h0 : ∃ J : E.M (ϖ.prism a) →+ TW (OW l O) T, ∀ x, J x = kappa T (jA (E.tr (ϖ.toAinf a) x)) :=
    ⟨(kappa T).comp (jA.toAddMonoidHom.comp (E.tr (ϖ.toAinf a)).toAddMonoidHom), fun _ => rfl⟩
  obtain ⟨J, hJ⟩ := h0
  have hi : Function.Injective J := by
    have := E.proj (ainfObj (ϖ.field a))
    have := E.proj (ϖ.prism a)
    intro x y h
    rw [hJ, hJ] at h
    exact BKCoord.semiBC_injective (E.tr_bc (ϖ.toAinf a)) (BKCoord.ev_injective ϖ)
      (BKCoord.semiBC_injective H.bc inclW_injective ((kappa_bijective T).1 h))
  have hJo : ∀ c x, J ((oE c).u (ϖ.prism a) x) = c • J x := fun c x => by
    have h3 := (congrArg jA ((oE c).u_tr (ϖ.toAinf a) x)).symm.trans (hoE c _)
    have h4 := (congrArg (kappa T) h3).trans (OfCrystal.kappa_mulZ T c _)
    rewrite [hJ, hJ]
    exact h4
  have hJs : ∀ (w : (ϖ.prism a).A) x, J (w • x) = ((1 : O) ⊗ₜ[ℤ_[l]] evW a ϖ w : OW l O) • J x :=
    fun w x => by
    have h3 := congrArg jA ((E.tr (ϖ.toAinf a)).map_smulₛₗ w x)
    have h4 := congrArg (kappa T) (h3.trans (jA.map_smulₛₗ _ _))
    have h5 := h4.trans (BKCoord.kappa_smul T _ _)
    rewrite [hJ, hJ]
    exact h5
  refine ⟨fun i => hi (by rw [hJo, one_smul]), ?_⟩
  intro P' f Q Q' _ _ c y c' y' heq R _ _ ψ hψ i
  have h1 : ∃ D : E.M (ϖ.prism a) →+ (ι → OW l O), ∀ x, D x = I.j.symm (J x) :=
    ⟨I.j.symm.toLinearMap.toAddMonoidHom.comp J, fun _ => rfl⟩
  obtain ⟨D, hD⟩ := h1
  have h2 : ∀ x k, ∃ z, Algebra.TensorProduct.map (AlgHom.id O O) (evW a ϖ) z = D x k := fun x k => by
    obtain ⟨m, hm, h⟩ := (him (J x)).1 ⟨x, hJ x⟩
    rw [hD, h, LinearEquiv.symm_apply_apply]
    exact exists_toW_eq t ϖ hm k
  have h3 : ∀ (w : (ϖ.prism a).A) x, D (w • x) = ((1 : O) ⊗ₜ[ℤ_[l]] evW a ϖ w : OW l O) • D x :=
    fun w x => (hD _).trans ((congrArg I.j.symm (hJs w x)).trans
      ((I.j.symm.map_smul _ _).trans (congrArg _ (hD x).symm)))
  have h4 : ∀ (o : O) j k, D ((oE o).u (ϖ.prism a) (b j)) k = o • if k = j then 1 else 0 := fun o j k => by
    obtain ⟨hm, h⟩ := hb j
    have h5 : I.j.symm (J (b j)) = toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩ :=
      I.j.symm_apply_eq.2 ((hJ _).trans h)
    have h6 : I.j.symm (o • J (b j)) = o • I.j.symm (J (b j)) := LinearMapClass.map_smul_of_tower _ _ _
    have h7 := ((hD _).trans (congrArg I.j.symm (hJo o (b j)))).trans (h6.trans (congrArg (o • ·) h5))
    exact (congrFun h7 k).trans (congrArg (o • ·) (toW_bas t ϖ j hm k))
  letI : Algebra ℤ_[l] (ϖ.prism a).A := (inferInstance : Algebra ℤ_[l] (Wq l a)⟦X⟧)
  obtain ⟨lam, hlam⟩ := indep_of_coord (Z := ℤ_[l]) (S := (ϖ.prism a).A) (E.tr_bc f) (evW a ϖ)
    (OfCrystal.ev_injective ϖ t K) ψ hψ D h2 h3 (fun o j => (oE o).u (ϖ.prism a) (b j)) h4
  simp only [FHom.u_tr] at heq
  exact (hlam Q c y i).symm.trans ((congrArg (lam · i) heq).trans (hlam Q' c' y' i))

end GlobalTheory.CrysIndep
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.breuilKisinPrism_crystal_coordinates : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : GlobalTheory.BKReal.Lat a O K ϖ) (I : Ident t ϖ P T), GlobalTheory.Published.BhattScholzeCrystallineLattices → IsBK I → ∃ (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c ∧ (∀ x, c x ∈ P.M) ∧ (∀ m ∈ P.M, ∃ x, c x = m) ∧ (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) ∧ (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) ∧ (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) := by
  first | exact @GlobalTheory.BKCoord.main | exact GlobalTheory.BKCoord.main | (intros; apply GlobalTheory.BKCoord.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_prime_pow_smul_eq_tmul_of_frobenius_fixed_fil_zero : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [Algebra O K] [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (C : GlobalTheory.MemLoc.Core l) (z : TW (OB l O) T), TWmap (frobOB l O) T z = z → z ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} → ∃ (n : ℕ) (x : ↥T.L.T), (l : O) ^ n • z = (1 : OB l O) ⊗ₜ[O] x := by
  first | exact @GlobalTheory.CrisFixedLattice.exists_pow_smul_eq_one_tmul | exact GlobalTheory.CrisFixedLattice.exists_pow_smul_eq_one_tmul | (intros; apply GlobalTheory.CrisFixedLattice.exists_pow_smul_eq_one_tmul <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.exists_blochKato_cocycle_of_crys_deRham_pair : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ A : GRep ↥(GK K) ℚ_[l] LL O, ∀ d₁ ∈ Dcris (P.PD K) A.ρ, ∀ d₂ ∈ DdR (P.PD K) A.ρ, ∃ (x : A.V ⊗[ℚ_[l]] P.R.B) (y : A.V ⊗[ℚ_[l]] P.R.BdR) (c : ↥(GK K) → A.V), y ∈ FilV (P.PD K) (LL := LL) (V := A.V) 0 ∧ x - φVB (P.PD K) (LL := LL) (V := A.V) x = d₁ ∧ ιV (P.PD K) (LL := LL) (V := A.V) x - y = d₂ ∧ c ∈ finiteCocycles (P.PD K) A.ρ ∧ ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) A.ρ g x - x := by
  first | exact @GlobalTheory.FundDel.connecting_cocycle | exact GlobalTheory.FundDel.connecting_cocycle | (intros; apply GlobalTheory.FundDel.connecting_cocycle <;> assumption)
end
