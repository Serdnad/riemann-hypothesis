module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerSpannedByKappaLaurent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle006
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem UpperTheory.V.Pa.defUTest_smul {F : Type} [CommRing F] {e : ℕ} (c : F) (x : DD F e) :
    c • x = DD.C c * x := rfl

private def UpperTheory.V.Pa.defUTest_a (F : Type) [CommRing F] (e : ℕ) : DD F e →ₗ[F] F where
  toFun x := x.a
  map_add' _ _ := rfl
  map_smul' c x := by simp [defUTest_smul]

private def UpperTheory.V.Pa.defUTest_ep (F : Type) [CommRing F] {e : ℕ} (k : Fin e) : DD F e →ₗ[F] F where
  toFun x := x.ep k
  map_add' _ _ := rfl
  map_smul' c x := by simp [defUTest_smul]

private def UpperTheory.V.Pa.defUTest_ep' (F : Type) [CommRing F] {e : ℕ} (k : Fin e) : DD F e →ₗ[F] F where
  toFun x := x.ep' k
  map_add' _ _ := rfl
  map_smul' c x := by simp [defUTest_smul]

private def UpperTheory.V.Pa.defUTest_eta (F : Type) [CommRing F] (e : ℕ) : DD F e →ₗ[F] F where
  toFun x := x.eta
  map_add' _ _ := rfl
  map_smul' c x := by simp [defUTest_smul]

theorem UpperTheory.V.Pa.defUTest :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ (e : ℕ) (α : Fin e → S.Bh →+ S.F) (μ : Fin e → S.U.N →+ S.F) (Φ : S.U.N →+ S.F), (∀ k, α k ∈ S.Tp) → (∀ k, μ k ∈ S.La) → (∀ (b : S.Bh) y, Φ (b • y) = S.rF b * Φ y + ∑ k, α k b * μ k y) → ∃ (u : S.G.G₀ → Matrix (Fin S.n) (Fin S.n) (DD S.F e)) (ψ : ∀ v, Fin S.n → S.L.Gv v →* (DD S.F e)ˣ), DefU S.h S.x u ψ ∧ (∀ k, epC S.h S.x u k = S.laC (μ k)) ∧ ∀ k, epC' S.h S.x u k = S.alC (α k) := by
  intro l _ S e α μ Φ hα hμ hΦ
  obtain ⟨θ, hT, hθ⟩ := testEx l S e α μ Φ hα hμ hΦ
  obtain ⟨_, hE, _, hψ, hm⟩ := testVal l S (DD S.F e) (DD.aug S.F e) θ hT
  obtain ⟨hord, hine, _, _, _⟩ := vrRel l S
  have hp := prAdd l S
  have hB : ∀ b : S.B, S.pr1 (algebraMap S.B S.U.AA b) = 0 := by
    intro b
    have h1 := (hp.2.1 (algebraMap S.B S.Bh b) 0).2
    simpa [← IsScalarTower.algebraMap_apply] using h1
  let u : S.G.G₀ → Matrix (Fin S.n) (Fin S.n) (DD S.F e) := fun g => (S.U.vr g).map θ
  let ψ : ∀ v, Fin S.n → S.L.Gv v →* (DD S.F e)ˣ := fun v i =>
    (Units.map (θ.comp (algebraMap S.B S.U.AA)).toMonoidHom).comp (S.u.ψ v i)
  refine ⟨u, ψ, ?_, ?_, ?_⟩
  · refine
      { one := by simp [u]
        mul := by intro g g'; simp [u, Matrix.map_mul]
        red := ?_
        even := ?_
        form := ?_
        ine := ?_
        ψ_red := ?_
        ψ_even := ?_
        ψ_mu := ?_
        ord := ?_
        bnd := ?_ }
    · intro g
      ext i j
      simp only [u, Matrix.map_apply, hθ]
      exact (prVr l S g i j).1
    · intro g i j
      obtain ⟨_, h1, h2⟩ := prVr l S g i j
      constructor
      · intro hij
        simp only [u, Matrix.map_apply, hθ]
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          first
          | (intro h; exact absurd h (by decide))
          | (intro _; funext k; simp [h1 hij])
          | (intro _; simp [h1 hij])
      · intro hij
        simp only [u, Matrix.map_apply, hθ]
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          first
          | (intro h; exact absurd h (by decide))
          | (intro _; funext k; simp [h2 hij])
          | (intro _; simp [h2 hij])
    · intro g
      have h := congrArg θ.mapMatrix (S.U.form g)
      simp only [map_mul, RingHom.mapMatrix_apply, Matrix.transpose_map] at h
      rw [show ((S.U.vr g).map θ)ᵀ = ((S.U.vr g)ᵀ).map θ from (Matrix.transpose_map).symm]
      refine h.trans (Matrix.ext fun i j => ?_)
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.one_apply_eq, map_one, mul_one]
        exact (hE g _).trans rfl
      · simp only [Matrix.one_apply_ne hij, map_zero, mul_zero]
    · intro w g hg
      simp [u, hine w g hg]
    · intro v i g
      exact hψ v i g
    · intro v i g
      simp only [ψ, MonoidHom.comp_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        RingHom.coe_comp, Function.comp_apply, hθ, hB]
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        first
        | (intro h; exact absurd h (by decide))
        | (intro _; funext k; simp)
        | (intro _; simp)
    · intro v i g hg
      exact Units.ext (hm v i g hg)
    · intro v g
      have h := congrArg θ.mapMatrix (hord v g)
      rw [map_list_prod, map_zero, List.map_ofFn] at h
      refine Eq.trans ?_ h
      refine congrArg List.prod (congrArg List.ofFn (funext fun i => Matrix.ext fun a b => ?_))
      by_cases hab : a = b
      · subst hab
        simp [u, ψ, Matrix.algebraMap_matrix_apply, Matrix.sub_apply]
      · simp [u, ψ, Matrix.algebraMap_matrix_apply, Matrix.sub_apply, hab]
    · intro i j
      exact ⟨trBnd l S _ _ θ hT (defUTest_a S.F e) i j,
        fun k => trBnd l S _ _ θ hT (defUTest_ep S.F k) i j,
        fun k => trBnd l S _ _ θ hT (defUTest_ep' S.F k) i j,
        trBnd l S _ _ θ hT (defUTest_eta S.F e) i j⟩
  · intro k
    funext γ
    simp only [epC, Ctx.laC, u, Matrix.map_map]
    congr 1
    ext i j
    simp [hθ]
  · intro k
    funext γ
    simp only [epC', Ctx.alC, u, Matrix.map_map]
    congr 1
    ext i j
    simp [hθ]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.k2F :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), K2 h k → EvenCocyclesLiftLaurent h k := by
  intro l _ L G G0 h n x k hK z hz
  set f := algebraMap x.A x.Fr with hf
  have ht : f x.t ≠ 0 := by
    intro h0
    apply PowerSeries.X_ne_zero (R := x.K)
    exact IsFractionRing.injective x.A x.Fr (h0.trans (map_zero f).symm)
  choose s₀ hs using fun i j => selScale l L G G0 h n x true (z i j) (hz i j).1 (hz i j).2
  set S := Finset.univ.sup (fun p : Fin (k.g + 1) × Fin k.g => s₀ p.1 p.2) with hSdef
  have hS : ∀ i j, s₀ i j ≤ S := fun i j =>
    Finset.le_sup (f := fun p : Fin (k.g + 1) × Fin k.g => s₀ p.1 p.2) (Finset.mem_univ (i, j))
  choose z' hz' hzz using fun i j => hs i j S (hS i j)
  obtain ⟨c, hc, Ψ, hΨ, hΨe⟩ := hK z' (fun i j => hz' i j)
  obtain ⟨hΨ1, hΨ2⟩ := selMap2 l L G G0 h n x k Ψ hΨ
  refine ⟨fun i => f (c i) * f x.t ^ S, ?_, _, hΨ1, hΨ2, ?_⟩
  · intro h0
    apply hc
    funext i
    have e := congrFun h0 i
    rcases mul_eq_zero.1 e with e | e
    · exact IsFractionRing.injective x.A x.Fr (e.trans (map_zero f).symm)
    · exact absurd e (pow_ne_zero S ht)
  · intro j γ a b
    have hz2 : ∀ i, f (z' i j γ a b) = f x.t ^ S * z i j γ a b := fun i => by
      have e := congrArg (fun M => M a b) (hzz i j γ)
      simpa using e
    show f ((Ψ γ a b).ep' j) = _
    rw [hΨe j γ a b]

    simp only [Matrix.sum_apply, Finset.sum_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
    map_sum, map_mul, hz2]
    refine Finset.sum_congr rfl fun i _ => by ring
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.k3F :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), K3 h k → SelmerSpannedByKappaLaurent h k := by
  intro l _ L G G0 h n x k hK z hz hb
  obtain ⟨s₀, hs⟩ := selScale l L G G0 h n x false z hz hb
  obtain ⟨z', hz', hzz⟩ := hs s₀ le_rfl
  obtain ⟨s', c, Y, hY, hYt, hYe⟩ := hK z' hz'
  set f := algebraMap x.A x.Fr with hf
  have ht : f x.t ≠ 0 := by
    intro h0
    apply PowerSeries.X_ne_zero (R := x.K)
    exact IsFractionRing.injective x.A x.Fr (h0.trans (map_zero f).symm)
  have hsm : ∀ (a : x.A) (M : Matrix (Fin n) (Fin n) x.A), f.mapMatrix (a • M) = f a • M.map f := by
    intro a M
    ext i j
    simp
  have key : ∀ g, x.t ^ s' • z' g - ∑ j, c j • k.κ j (h.p₀ g) =
      x.ρX x.A (h.p₀ g) * Y * x.ρX x.A (h.p₀ g⁻¹) - Y := by
    intro g
    have e := congrFun hYe g
    simpa [dY, Finset.sum_apply] using e
  have key2 : ∀ g, f x.t ^ s' • (z' g).map f - ∑ j, f (c j) • kapF h k j g =
      x.ρX x.Fr (h.p₀ g) * Y.map f * x.ρX x.Fr (h.p₀ g⁻¹) - Y.map f := by
    intro g
    have e := congrArg f.mapMatrix (key g)

    simpa [map_sub, map_mul, map_sum, hsm, kapF, NP.ρX, Matrix.map_map, RingHom.mapMatrix_apply] using e
  set u := (f x.t ^ (s' + s₀))⁻¹ with hu
  refine ⟨fun j => u * f (c j), u • Y.map f, ?_, ?_, ?_⟩
  · intro i j
    obtain ⟨h1, h2⟩ := hY i j
    refine ⟨fun hij => ?_, fun _ => Submodule.mem_top⟩
    have h3 := h1 hij
    rw [Submodule.mem_bot] at h3 ⊢
    simp [h3]
  · ext i j
    have h3 := congrFun (congrFun hYt i) j
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h3
    simp [Matrix.transpose_apply, h3]
  · funext g
    have e := key2 g
    rw [hzz g, smul_smul, ← pow_add] at e
    simp only [dY, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, ← e, smul_sub, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero _ ht), one_smul, Finset.smul_sum]
    simp [smul_smul]
end
