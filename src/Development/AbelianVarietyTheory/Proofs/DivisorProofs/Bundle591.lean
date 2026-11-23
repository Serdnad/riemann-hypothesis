module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Mathlib.GroupTheory.SemidirectProduct
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle372
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle041
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle205
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle003
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle493
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Mathlib.Topology.LocallyConstant.Algebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveCechPoincareRichChartsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle337
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_global_unit_ratio_generic_lineBundle_isos : ∀ (X Y : Scheme.{0}) (β : Y ⟶ X) (P M : LB X) (N : LB Y), P.IsLB → M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull β) N) (w₁ : LB.Iso (P.pull β) N) (v : LB.Iso P M), w.IsGen → w₁.IsGen → v.IsGen → ∃ u : Γ(Y, ⊤)ˣ, ∀ (n : N.ι) (i : P.ι) (m : M.ι) (hle : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ β ⁻¹ᵁ (M.U m ⊓ P.U i)), GlobalTheory.AbLaw.rs _ (inf_le_left : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ N.U n ⊓ (P.pull β).U (fun _ => i)) (w₁.s (n, fun _ => i)).val = GlobalTheory.AbLaw.rs _ (le_top : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ ⊤) (u : Γ(Y, ⊤)) * (β.appLE (M.U m ⊓ P.U i) _ hle).hom (v.s (m, i)).val * GlobalTheory.AbLaw.rs _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ N.U n ⊓ (M.pull β).U (fun _ => m)) (w.s (n, fun _ => m)).val := by
  first | exact @GlobalTheory.GenIsoRatio.ratio | exact GlobalTheory.GenIsoRatio.ratio | (intros; apply GlobalTheory.GenIsoRatio.ratio <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.StableExt

theorem isSSRep_of_finite {G : Type} [Group G] [Finite G] {d : ℕ} (ρ : G →* GL (Fin d) ℂ) :
    Formalism.MainNotions.N.IsSSRep ρ := by
  haveI : (⊥ : Subgroup G).FiniteIndex := inferInstance
  apply GlobalTheory.FiniteIndexSemisimple.isSSRep_of_finiteIndex ρ (⊥ : Subgroup G)
  intro W _
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
  refine ⟨W', fun g v hv => ?_, hW'⟩
  have hg : (g : G) = 1 := Subgroup.mem_bot.mp g.2
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, hg, map_one, Units.val_one, Matrix.one_mulVec]
  exact hv

theorem commute_aeval {n : ℕ} {M B : Matrix (Fin n) (Fin n) ℂ} (h : Commute M B) (p : ℂ[X]) :
    Commute M (aeval B p) := by
  rw [aeval_eq_sum_range]
  exact Commute.sum_right _ _ _ fun i _ => (h.pow_right i).smul_right _

theorem exists_ext : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ),
    (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ Y : G → ℂ, IsChar ℂ ℂ Y → (∀ g, Y (φ s g) = Y g) →
    ∃ Z : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ Z ∧ ∀ g, Z (inl g) = Y g := by
  intro G Γ _ _ _ _ φ s hs Y hY hYs
  obtain ⟨d, ρ, hρ⟩ := (GlobalTheory.BI.matrixChar_iff_isChar G Y).mpr hY
  let ρ' : G →* GL (Fin d) ℂ := ρ.comp (φ s).toMonoidHom
  obtain ⟨A, hA⟩ := GlobalTheory.TraceConj.conj_of_trace_eq G ℂ d ρ ρ' (isSSRep_of_finite ρ)
    (isSSRep_of_finite ρ') (fun g => by
      show _ = Matrix.trace ((ρ (φ s g) : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)
      rw [← hρ, ← hρ, hYs])
  have hA' : ∀ g, ρ (φ s g) = A * ρ g * A⁻¹ := fun g => hA g
  have hAk : ∀ k : ℕ, ∀ g, ρ (((φ s) ^ k) g) = A ^ k * ρ g * (A ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih => intro g; rw [pow_succ', MulAut.mul_apply, hA', ih]; group
  set l := orderOf s with hl_def
  have hl : 0 < l := orderOf_pos s
  have hφl : (φ s) ^ l = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hB : ∀ g, A ^ l * ρ g = ρ g * A ^ l := by
    intro g
    have := hAk l g
    rw [hφl, MulAut.one_apply] at this
    calc A ^ l * ρ g = (A ^ l * ρ g * (A ^ l)⁻¹) * A ^ l := by group
      _ = ρ g * A ^ l := by rw [← this]
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_poly_pow_mul_eq_one' d l ((A ^ l : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) hl (Units.isUnit _)
  set Bm : Matrix (Fin d) (Fin d) ℂ := ((A ^ l : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) with hBm
  set C : Matrix (Fin d) (Fin d) ℂ := aeval Bm p with hC
  have hCA : Commute ((A : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) C := by
    apply commute_aeval
    rw [hBm, Units.val_pow_eq_pow_val]
    exact (Commute.refl _).pow_right l
  have hCρ : ∀ g, Commute ((ρ g : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) C := by
    intro g
    apply commute_aeval
    have := congrArg (fun x : GL (Fin d) ℂ => (x : Matrix (Fin d) (Fin d) ℂ)) (hB g)
    simp only [Units.val_mul] at this
    exact this.symm
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl
  have h1 : C * (C ^ (l - 1) * Bm) = 1 := by
    rw [← mul_assoc, ← pow_succ', hl1]; exact hp
  let Cu : GL (Fin d) ℂ := ⟨C, C ^ (l - 1) * Bm, h1, mul_eq_one_comm.mp h1⟩
  have hCuA : A * Cu = Cu * A := Units.ext (hCA.eq)
  have hCuρ : ∀ g, Cu * ρ g = ρ g * Cu := fun g => Units.ext ((hCρ g).eq.symm)
  have hCuB : Cu ^ l * A ^ l = 1 := Units.ext (by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one]; exact hp)
  set A' : GL (Fin d) ℂ := A * Cu with hA'def
  have hA'l : A' ^ l = 1 := by
    rw [hA'def, (show Commute A Cu from hCuA).mul_pow, ((show Commute A Cu from hCuA).pow_pow l l).eq]
    exact hCuB
  have hA's : ∀ g, ρ (φ s g) = A' * ρ g * A'⁻¹ := by
    intro g
    rw [hA', hA'def, mul_inv_rev]
    calc A * ρ g * A⁻¹ = A * (ρ g * Cu) * Cu⁻¹ * A⁻¹ := by group
      _ = A * Cu * ρ g * (Cu⁻¹ * A⁻¹) := by rw [← hCuρ g]; group
  let σ : Γ →* GL (Fin d) ℂ := monoidHomOfForallMemZpowers hs (orderOf_dvd_of_pow_eq_one hA'l)
  have hσs : σ s = A' := monoidHomOfForallMemZpowers_apply_gen hs _
  let H : Subgroup Γ :=
    { carrier := {t | ∀ g, ρ (φ t g) = σ t * ρ g * (σ t)⁻¹}
      mul_mem' := by
        intro a b ha hb g
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, MulAut.mul_apply, ha, hb, map_mul]; group
      one_mem' := by intro g; simp
      inv_mem' := by
        intro a ha g
        simp only [Set.mem_setOf_eq] at *
        have := ha ((φ a⁻¹) g)
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at this
        rw [map_inv σ]
        calc ρ (φ a⁻¹ g) = (σ a)⁻¹ * (σ a * ρ (φ a⁻¹ g) * (σ a)⁻¹) * σ a := by group
          _ = (σ a)⁻¹ * ρ g * ((σ a)⁻¹)⁻¹ := by rw [← this]; group }
  have hsH : s ∈ H := fun g => by rw [hσs]; exact hA's g
  have hall : ∀ t, ∀ g, ρ (φ t g) = σ t * ρ g * (σ t)⁻¹ := fun t => (Subgroup.zpowers_le.mpr hsH) (hs t)
  let Λ : G ⋊[φ] Γ →* GL (Fin d) ℂ := SemidirectProduct.lift ρ σ (fun t => by
    ext g : 1
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hall t g)
  refine ⟨fun x => Matrix.trace ((Λ x : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ), ?_, ?_⟩
  · exact (GlobalTheory.BI.matrixChar_iff_isChar _ _).mp ⟨d, Λ, fun x => rfl⟩
  · intro g
    simp only [Λ, SemidirectProduct.lift_inl]
    exact (hρ g).symm

end GlobalTheory.StableExt
end
end

section

section

open Finset

namespace GlobalTheory.PsCo.PcEF.VandermondeCompactNoncompactSplit

variable {n : ℕ}

theorem lhs_eq (t : Fin n → ℂ) :
    (∏ a, ∏ b ∈ Finset.Ioi a, (t a - t b)) =
      ∏ x : Fin n × Fin n, if x.1 < x.2 then t x.1 - t x.2 else 1 := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_filter]
  congr 1
  ext b
  simp

theorem wden_eq (ε : Fin n → Bool) (t : Fin n → ℂ) :
    ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε t =
      ∏ x : Fin n × Fin n, if x.1 < x.2 ∧ ε x.1 = ε x.2 then t x.1 - t x.2 else 1 := by
  rw [Fintype.prod_prod_type]
  rfl

theorem mode_eq (ε : Fin n → Bool) (t : Fin n → ℂ) :
    (∏ x : GlobalTheory.PsCo.Pc1.Mode ε, (t x.1.1 - t x.1.2)) =
      ∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false then t x.1 - t x.2 else 1 := by
  rw [← Finset.prod_filter]
  exact (Finset.prod_subtype _ (fun x => by simp) (fun x : Fin n × Fin n => t x.1 - t x.2)).symm

theorem sign_eq (ε : Fin n → Bool) :
    (∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 then (-1 : ℂ) else 1) =
      (-1) ^ ReciprocityTheory.ChartRestriction.DS.TRGap.sDeg ε := by
  rw [← Finset.prod_filter, Finset.prod_const]
  rfl

theorem swap_eq (ε : Fin n → Bool) (t : Fin n → ℂ) :
    (∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 then t x.2 - t x.1 else 1) =
      ∏ x : Fin n × Fin n, if ε x.2 = true ∧ ε x.1 = false ∧ x.1 < x.2 then t x.1 - t x.2 else 1 :=
  Fintype.prod_equiv (Equiv.prodComm _ _) _ _ (fun _ => rfl)

theorem mode_split (ε : Fin n → Bool) (t : Fin n → ℂ) :
    (∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false then t x.1 - t x.2 else 1) =
      (∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.1 < x.2 then t x.1 - t x.2 else 1) *
        ((∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 then (-1 : ℂ) else 1) *
          ∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 then t x.2 - t x.1 else 1) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  obtain ⟨a, b⟩ := x
  rcases lt_trichotomy a b with h | rfl | h
  · cases h1 : ε a <;> cases h2 : ε b <;> simp [h, lt_asymm h]
  · cases h1 : ε a <;> simp
  · cases h1 : ε a <;> cases h2 : ε b <;> simp [h, lt_asymm h]

theorem lhs_split (ε : Fin n → Bool) (t : Fin n → ℂ) :
    (∏ x : Fin n × Fin n, if x.1 < x.2 then t x.1 - t x.2 else 1) =
      (∏ x : Fin n × Fin n, if x.1 < x.2 ∧ ε x.1 = ε x.2 then t x.1 - t x.2 else 1) *
        ((∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.1 < x.2 then t x.1 - t x.2 else 1) *
          ∏ x : Fin n × Fin n, if ε x.2 = true ∧ ε x.1 = false ∧ x.1 < x.2 then t x.1 - t x.2 else 1) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  obtain ⟨a, b⟩ := x
  rcases lt_trichotomy a b with h | rfl | h
  · cases h1 : ε a <;> cases h2 : ε b <;> simp [h]
  · simp
  · cases h1 : ε a <;> cases h2 : ε b <;> simp [lt_asymm h]

end GlobalTheory.PsCo.PcEF.VandermondeCompactNoncompactSplit

namespace GlobalTheory.PsCo.PcEF


open VandermondeCompactNoncompactSplit in
theorem vandermonde_splits_compactNoncompact (n : ℕ) (ε : Fin n → Bool) (t : Fin n → ℂ) :
    (∏ a, ∏ b ∈ Finset.Ioi a, (t a - t b)) =
      ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε t *
        ((-1) ^ ReciprocityTheory.ChartRestriction.DS.TRGap.sDeg ε *
          ∏ x : GlobalTheory.PsCo.Pc1.Mode ε, (t x.1.1 - t x.1.2)) := by
  rw [lhs_eq, wden_eq, mode_eq, mode_split, sign_eq, swap_eq, lhs_split]
  have hs : ((-1 : ℂ) ^ ReciprocityTheory.ChartRestriction.DS.TRGap.sDeg ε) * (-1) ^ ReciprocityTheory.ChartRestriction.DS.TRGap.sDeg ε = 1 := by
    rw [← mul_pow]; norm_num
  generalize (-1 : ℂ) ^ ReciprocityTheory.ChartRestriction.DS.TRGap.sDeg ε = s at hs ⊢
  linear_combination (-((∏ x : Fin n × Fin n, if x.1 < x.2 ∧ ε x.1 = ε x.2 then t x.1 - t x.2 else 1) *
    (∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.1 < x.2 then t x.1 - t x.2 else 1) *
    ∏ x : Fin n × Fin n, if ε x.2 = true ∧ ε x.1 = false ∧ x.1 < x.2 then t x.1 - t x.2 else 1)) * hs

end GlobalTheory.PsCo.PcEF

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts.DegZero

theorem sub_rel {M : Type} [AddCommGroup M] {p0 p1 u0 u1 v0 v1 w z0 z1 : M}
    (c0 : p0 = u0 + w) (c0' : p0 = v0 + z0) (c1 : p1 = u1 + w) (c1' : p1 = v1 + z1) :
    u0 - u1 = v0 - v1 + (z0 - z1) := by
  have e0 : u0 = v0 + z0 - w := eq_sub_of_add_eq (c0.symm.trans c0')
  have e1 : u1 = v1 + z1 - w := eq_sub_of_add_eq (c1.symm.trans c1')
  rw [e0, e1]; abel

theorem sub_sub_eq_of_sub_eq_addCommGroup {M : Type} [AddCommGroup M] {h0 h1 j0 j1 d X : M}
    (e : h0 - h1 = d) (e' : j1 - j0 = d) : h0 - (X - j0) = h1 - (X - j1) := by
  have a0 : h0 = d + h1 := eq_add_of_sub_eq e
  have a1 : j1 = d + j0 := eq_add_of_sub_eq e'
  rw [a0, a1]; abel

theorem eq_inr {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
    (x : TrivSqZeroExt O M) (hx : x.fst = 0) : x = TrivSqZeroExt.inr x.snd :=
  TrivSqZeroExt.ext hx rfl

theorem tszeSec_sub_inl {g : ℕ} {O : Type} [CommRing O] [Algebra ℂ O] (D : Fin g → Derivation ℂ O O) (x : O) :
    tszeSec D x - TrivSqZeroExt.inl x = TrivSqZeroExt.inr fun a ↦ D a x := by
  show TrivSqZeroExt.inl x + TrivSqZeroExt.inr (fun a ↦ D a x) - TrivSqZeroExt.inl x = _
  abel

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}

theorem translationChartShiftSubstitution_comp_degZero {k k' k'' : K.K} (e : K.le 0 k' k) (e' : K.le 0 k'' k') (e'' : K.le 0 k'' k)
    (f : Hol (K.W k)) : K.sh e' (K.sh e f) = K.sh e'' f :=
  Hol.ext_fn fun p hp ↦ by
    rw [fn_sh e' _ hp, fn_sh e _ (K.maps e' p hp), fn_sh e'' _ hp]
    simp only [F.shift_zero]

theorem ptHom_refl_triv (k : K.K) : ptHom (K.triv k) (K.le_refl k) = 𝟙 (K.triv k) :=
  hom_ext (fun c ↦ sh_refl (K.le_refl k) c) rfl

theorem ptHom_comp0 {k k' k'' : K.K} (e : K.le 0 k' k) (e' : K.le 0 k'' k') (e'' : K.le 0 k'' k) :
    ptHom (K.triv k') e ≫ ptHom (K.triv k'') e' = ptHom (K.triv k'') e'' :=
  hom_ext (fun c ↦ translationChartShiftSubstitution_comp_degZero e e' e'' c) (add_zero (0 : Λ))

def corr (h : C1 K.Oc) (G : C0 K.Oc) : C1 K.Oc := fun T T' φ ↦ h T T' φ - (G T' - φ.φ (G T))

theorem zero_id (h : C1 K.Oc)
    (hc : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) (T : K.Obj) : h T T (𝟙 T) = 0 := by
  have e := hc T T T (𝟙 T) (𝟙 T) rfl rfl
  rw [Category.id_comp] at e
  change (h T T (𝟙 T) : T.C) = h T T (𝟙 T) + h T T (𝟙 T) at e
  exact (add_eq_left.mp e.symm)

theorem corr_cocycle (h : C1 K.Oc) (G : C0 K.Oc)
    (hc : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) :
    ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      corr h G T T'' (φ ≫ ψ) = ψ.φ (corr h G T T' φ) + corr h G T' T'' ψ := by
  intro T T' T'' φ ψ hφ hψ
  change (h T T'' (φ ≫ ψ) : T''.C) - (G T'' - ψ.φ (φ.φ (G T))) =
    ψ.φ ((h T T' φ : T'.C) - (G T' - φ.φ (G T))) + ((h T' T'' ψ : T''.C) - (G T'' - ψ.φ (G T')))
  rw [hc T T' T'' φ ψ hφ hψ, map_sub, map_sub]
  abel

theorem vanish (h : C1 K.Oc)
    (hc : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ)
    (v1 : ∀ T : K.Obj, h _ _ (ptHom T (K.le_refl T.k)) = 0)
    (v2 : ∀ k k' (e : K.le 0 k' k), h _ _ (ptHom (K.triv k') e) = 0)
    (v3 : ∀ k, h _ _ (jet0 k) = h _ _ (jet1 k)) (T T' : K.Obj) (φ : T ⟶ T') (hφ : φ.deg = 0) :
    h T T' φ = 0 := by
  have hm := GlobalTheory.T.cochain_eq_of_same_degree_chartMorphism K h 0 (fun k T χ hχ ↦ by
    rw [hc _ _ _ (jet0 k) χ rfl hχ, hc _ _ _ (jet1 k) χ rfl hχ, v3 k])
  have v5 : ∀ (k : K.K) (T : K.Obj) (f : K.triv k ⟶ T), f.deg = 0 → h _ _ f = 0 := by
    intro k T f hd
    have e : K.le 0 T.k k := hd ▸ Charts.Hom.le f
    have hs : ∀ c : Hol (K.W k), K.sh (Charts.Hom.le f) c = K.sh (K.le_refl T.k) (K.sh e c) := fun c ↦ by
      rw [sh_refl]
      exact Hol.ext_fn fun p hp ↦ by rw [fn_sh (Charts.Hom.le f) c hp, fn_sh e c hp, hd]
    have hcomp : ptHom T (Charts.Hom.le f) = ptHom (K.triv T.k) e ≫ ptHom T (K.le_refl T.k) :=
      hom_ext (fun c ↦ congrArg T.ρ (hs c)) (hd.trans (add_zero (0 : Λ)).symm)
    rw [hm k T f hd, hcomp, hc _ _ _ _ _ rfl rfl, v2, v1, map_zero, add_zero]
  have e := hc _ _ _ (ptHom T (K.le_refl T.k)) φ rfl hφ
  rw [v5 _ _ _ ((zero_add φ.deg).trans hφ), v1, map_zero, zero_add] at e
  exact e.symm

def jetDiff (h : C1 K.Oc) (k : K.K) : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)) :=
  h _ _ (jet0 k) - h _ _ (jet1 k)

def trans0 (h : C1 K.Oc) (k k' : K.K) (e : K.le 0 k' k) : Hol (K.W k') := h _ _ (ptHom (K.triv k') e)

theorem jetDiff_sh (h : C1 K.Oc)
    (hc : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) (k k' : K.K) (e : K.le 0 k' k) (i : Fin g) :
    (jetDiff h k').snd i - K.sh e ((jetDiff h k).snd i) = dw i (trans0 h k k' e) := by
  obtain ⟨χ, hχ, h0, h1, hx⟩ := GlobalTheory.T.exists_jet_morphism_extending_translation K e
  have c0 := hc _ _ _ (jet0 k) χ rfl hχ
  have c1 := hc _ _ _ (jet1 k) χ rfl hχ
  rw [h0] at c0
  rw [h1] at c1
  have key := sub_rel c0 (hc _ _ _ (ptHom (K.triv k') e) (jet0 k') rfl rfl) c1
    (hc _ _ _ (ptHom (K.triv k') e) (jet1 k') rfl rfl)
  have key' : χ.φ (jetDiff h k) = (jet0 k').φ (trans0 h k k' e) - (jet1 k').φ (trans0 h k k' e) + jetDiff h k' :=
    (map_sub χ.φ _ _).trans key
  have s := (hx (jetDiff h k)).2 i
  rw [key'] at s
  have s' : (0 : Hol (K.W k')) - (tszeSec (g := g) dw (trans0 h k k' e)).snd i + (jetDiff h k').snd i =
      K.sh e ((jetDiff h k).snd i) := s
  rw [snd_tszeSec] at s'
  rw [← s']
  abel

def gauge (h : C1 K.Oc) (G₀ : ∀ k, Hol (K.W k)) : C0 K.Oc :=
  fun T ↦ (T.ρ (G₀ T.k) + (h _ _ (ptHom T (K.le_refl T.k)) : T.C) : T.C)

theorem exists_gauge : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → K.Based → ∀ (h : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∃ G : C0 K.Oc, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → h T T' φ = G T' - φ.φ (G T) := by
  intro I _ g Λ _ F K hR hB h hc
  have hcl := fun k ↦ GlobalTheory.T.connectionForm_degZeroCocycle_closed K h hc k (jetDiff h k) rfl
  obtain ⟨G₀, hd, ha⟩ := GlobalTheory.T.exists_primitive_cech_poincare_rich_charts K hR hB (trans0 h) (fun k ↦ (jetDiff h k).snd)
    (fun k k' k'' e e' e'' ↦ by
      have c := hc _ _ _ (ptHom (K.triv k') e) (ptHom (K.triv k'') e') rfl rfl
      rw [ptHom_comp0 e e' e''] at c
      exact c)
    (fun k i j ↦ (hcl k).2 i j) (jetDiff_sh h hc)
  have gt : ∀ k, gauge h G₀ (K.triv k) = G₀ k := fun k ↦ by
    have z : h _ _ (ptHom (K.triv k) (K.le_refl k)) = 0 := by
      rw [ptHom_refl_triv]; exact zero_id h hc _
    exact (congrArg (fun x : Hol (K.W k) ↦ G₀ k + x) z).trans (add_zero _)
  refine ⟨gauge h G₀, fun T T' φ hφ ↦ sub_eq_zero.mp
    (vanish (corr h (gauge h G₀)) (corr_cocycle h _ hc) (fun T ↦ ?_) (fun k k' e ↦ ?_) (fun k ↦ ?_) T T' φ hφ)⟩
  · have z : (ptHom T (K.le_refl T.k)).φ (gauge h G₀ (K.triv T.k)) = T.ρ (G₀ T.k) := by
      rw [gt]; exact congrArg T.ρ (sh_refl (K.le_refl T.k) _)
    unfold corr
    rw [z]
    exact sub_eq_zero.mpr (add_sub_cancel_left (G := T.C) _ _).symm
  · unfold corr
    rw [gt, gt]
    exact sub_eq_zero.mpr (ha k k' e)
  · unfold corr
    rw [gt]
    refine sub_sub_eq_of_sub_eq_addCommGroup (d := TrivSqZeroExt.inr (jetDiff h k).snd) (eq_inr (jetDiff h k) (hcl k).1) ?_
    have z0 : (jet0 k).φ (G₀ k) = TrivSqZeroExt.inl (G₀ k) :=
      congrArg TrivSqZeroExt.inl (sh_refl (K.le_refl k) (G₀ k))
    rw [z0]
    exact (tszeSec_sub_inl dw (G₀ k)).trans (congrArg TrivSqZeroExt.inr (funext (hd k)))

end GlobalTheory.AnPer.Charts.DegZero
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.sec_exists_of_isLocallyConstant_locallyConstant : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] (B : Type) [CommRing B], (∀ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), IsLocallyConstant (fun x : X => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t)) ∧ Function.Injective (fun (t : Sec F (Spec (CommRingCat.of (LocallyConstant X B)))) (x : X) => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t) ∧ ∀ ψ : X → Sec F (Spec (CommRingCat.of B)), IsLocallyConstant ψ → ∃ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), ∀ x, Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t = ψ x := by
  first | (exact @GlobalTheory.EtC.sec_locallyConstant) | (exact GlobalTheory.EtC.sec_locallyConstant) | (intros; apply GlobalTheory.EtC.sec_locallyConstant  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

noncomputable def coAugNat {J : Type} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{0}) :
    (D ⋙ Arrow.leftFunc) ⋙ CosimplicialObject.const CommRingCat.{0} ⟶ D ⋙ CosimplicialObject.cechConerve where
  app j := coAug (D.obj j).hom
  naturality i j f := by
    have h := (CosimplicialObject.augmentedCechConerve.map (D.map f)).w
    exact h

theorem wExact_of_finiteType_iso (N M : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ε : N ⟶ M)
    (hN : PreservesFilteredColimitsOfSize.{0, 0} N)
    (hε : ∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A))
    (hM : ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → WExact M (coAug g)) :
    ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → WExact N (coAug g) := by
  intro A B g hg
  obtain ⟨J, _, _, D, ι, ⟨hc⟩, hD⟩ := GlobalTheory.T.etaleFaithfullyFlat_filtered_colimit_finiteType A B g hg
  obtain ⟨⟨hU⟩, hX⟩ := GlobalTheory.EtC.isColimit_leftFunc_and_cechConerve_levels J D _ hc
  refine GlobalTheory.EtC.WExactColim.wExact_colimit CommRingCat.{0} N hN J (D ⋙ Arrow.leftFunc)
    (D ⋙ CosimplicialObject.cechConerve) (coAugNat D) (Arrow.leftFunc.mapCocone (Cocone.mk (Arrow.mk g) ι))
    (CosimplicialObject.cechConerve.mapCocone (Cocone.mk (Arrow.mk g) ι)) (coAug g) hU (fun k => hX k) ?_ ?_
  · intro j
    have h := (CosimplicialObject.augmentedCechConerve.map (ι.app j)).w
    exact h.symm
  · intro j
    obtain ⟨hj, hl, hr⟩ := hD j
    refine (GlobalTheory.EtC.wExact_congr CommRingCat.{0} _ _ (coAug (D.obj j).hom) N M ε (hε _ hl) (fun k => hε _ ?_)).2
      (hM _ _ _ hj)
    exact GlobalTheory.cechConerve_obj_finiteType_int _ _ (D.obj j).hom hr k

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleSpaceCohomology_stalk_local_classes : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (Θ Θ' : Over S ⥤ Spc) (α : Θ ⟶ Θ'), (∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i).left) → ContCone R F ((Θ).mapCone c)) → (∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i).left) → ContCone R F ((Θ').mapCone c)) → ∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R (α.app (Over.mk s)) F → ∀ (U : Over S), Etale U.hom → ∀ (g : Over.mk s ⟶ U) (n : ℤ), (∀ x : H R (Θ.obj U) F n, ∃ (V : Over S) (g' : Over.mk s ⟶ V) (h : V ⟶ U) (y : H R (Θ'.obj V) F n), Etale V.hom ∧ g' ≫ h = g ∧ pull R (α.app V) F n y = pull R (Θ.map h) F n x) ∧ ∀ y : H R (Θ'.obj U) F n, pull R (α.app U) F n y = 0 → ∃ (V : Over S) (g' : Over.mk s ⟶ V) (h : V ⟶ U), Etale V.hom ∧ g' ≫ h = g ∧ pull R (Θ'.map h) F n y = 0 := by
  first | (exact @GlobalTheory.EtC.stalk_local_classes) | (exact GlobalTheory.EtC.stalk_local_classes) | (intros; apply GlobalTheory.EtC.stalk_local_classes  <;> assumption)
end
