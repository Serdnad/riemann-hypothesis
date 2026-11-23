module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle036
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle018
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Valuation.Integral
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

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Stab

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

abbrev stabR (h : Hfin X u) : Subgroup (Hfin X u) := gamR X u ⊓ (kR X u).map (MulAut.conj h).toMonoidHom

theorem kset_one : (1 : X.B.I.Gf) ∈ X.B.I.Kset := (Formalism.UG.stabGL X.B.I.Lf).one_mem

theorem stab_kset {h g : Hfin X u} (hg : g ∈ (kR X u).map (MulAut.conj h).toMonoidHom) :
    ((h⁻¹ * g⁻¹ * h : Hfin X u) : X.B.I.Gf) ∈ X.B.I.Kset := by
  rw [mem_map_conj, mem_kR_iff] at hg
  have e : h⁻¹ * g⁻¹ * h = (h⁻¹ * g * h)⁻¹ := by group
  rw [e, Subgroup.coe_inv]
  exact kset_inv' X.B.I hg

variable {X u}

def matR {g : Hfin X u} (hg : g ∈ gamR X u) : GL (Fin X.B.I.n) X.B.I.E := Classical.choose (gamR_mat hg)

theorem matR_spec {g : Hfin X u} (hg : g ∈ gamR X u) :
    matR hg ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧
      X.B.I.fmat (g : X.B.I.Gf) = (matR hg : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) :=
  Classical.choose_spec (gamR_mat hg)

theorem matR_mem (h g : Hfin X u) (hg : g ∈ stabR X u h) :
    matE X (matR (Subgroup.mem_inf.1 hg).1) ∈ AH X u (lat X u h) := by
  obtain ⟨hM, hMf⟩ := matR_spec (Subgroup.mem_inf.1 hg).1
  have hfix : ∀ y ∈ fixSet X u, (matR (Subgroup.mem_inf.1 hg).1 : Matrix _ _ _).map
      (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) *ᵥ incl X.B.I y = incl X.B.I y := fun y hy => by
    rw [← hMf]; exact hfin_fix X u g y hy
  refine ⟨matE_isom X _ hM, fun a => matE_fix X u _ hfix _ (Or.inl (Or.inl ⟨a, rfl⟩)),
    fun a => matE_fix X u _ hfix _ (Or.inl (Or.inr ⟨a, rfl⟩)), matE_fix X u _ hfix _ (Or.inr rfl), ?_⟩
  have e : g * h * (h⁻¹ * g⁻¹ * h) = h := by group
  have := lat_act X u g h (h⁻¹ * g⁻¹ * h) _ hMf (stab_kset X u (Subgroup.mem_inf.1 hg).2)
  rw [e] at this
  exact this.symm

theorem card_stab (h : Hfin X u) : Nat.card ↥(stabR X u h) = Nat.card ↥(AH X u (lat X u h)) := by
  let Φ : ↥(stabR X u h) → ↥(AH X u (lat X u h)) := fun g =>
    ⟨matE X (matR (Subgroup.mem_inf.1 g.2).1), matR_mem h g g.2⟩
  have hinj : Function.Injective Φ := by
    intro g g' hgg
    have e1 : matE X (matR (Subgroup.mem_inf.1 g.2).1) = matE X (matR (Subgroup.mem_inf.1 g'.2).1) :=
      congrArg Subtype.val hgg
    have e2 := matE_inj X e1
    have f1 := (matR_spec (Subgroup.mem_inf.1 g.2).1).2
    have f2 := (matR_spec (Subgroup.mem_inf.1 g'.2).1).2
    have e3 : X.B.I.fmat ((g : Hfin X u) : X.B.I.Gf) = X.B.I.fmat ((g' : Hfin X u) : X.B.I.Gf) := by
      rw [f1, f2, e2]
    exact Subtype.ext (Subtype.ext (Subtype.ext (Units.ext e3)))
  have hsurj : Function.Surjective Φ := by
    rintro ⟨γ, hγ⟩
    obtain ⟨hi, he, hf, hz, hl⟩ := hγ
    set g := gOf X u γ hi he hf hz with hgdef
    have hgR : g ∈ gamR X u := (mem_gamR_iff X u g).2 ⟨glOf X γ, glOf_unitary X γ hi, rfl⟩
    have hlat : lat X u (g * h * 1) = lat X u h := by
      rw [lat_act X u g h 1 (glOf X γ) rfl (kset_one X), matE_glOf, hl]
    have hgK : g ∈ (kR X u).map (MulAut.conj h).toMonoidHom := by
      rw [mem_map_conj, mem_kR_iff]
      have hK := LatDictK.dict_K X ((h : X.B.I.Gf) * X.xu u) (((g * h * 1 : Hfin X u) : X.B.I.Gf) * X.xu u)
        (latOf X u h) (fun y => Iff.rfl) (fun y => by
          show y ∈ latOf X u h ↔ y ∈ latOf X u (g * h * 1)
          rw [← lat_coe X u h, ← lat_coe X u (g * h * 1), hlat])
      have e4 : ((h : X.B.I.Gf) * X.xu u)⁻¹ * (((g * h * 1 : Hfin X u) : X.B.I.Gf) * X.xu u) =
          (X.xu u)⁻¹ * ((h⁻¹ * g * h : Hfin X u) : X.B.I.Gf) * X.xu u := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
        group
      rw [e4] at hK
      have e5 : ((h⁻¹ * g * h : Hfin X u) : X.B.I.Gf) =
          X.xu u * ((X.xu u)⁻¹ * ((h⁻¹ * g * h : Hfin X u) : X.B.I.Gf) * X.xu u) * (X.xu u)⁻¹ := by group
      rw [e5]
      exact kset_mul' X.B.I (kset_mul' X.B.I (X.xu_K u) hK) (kset_inv' X.B.I (X.xu_K u))
    have hg : g ∈ stabR X u h := Subgroup.mem_inf.2 ⟨hgR, hgK⟩
    refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
    show matE X (matR (Subgroup.mem_inf.1 hg).1) = γ
    have f1 := (matR_spec (Subgroup.mem_inf.1 hg).1).2
    have e6 : matR (Subgroup.mem_inf.1 hg).1 = glOf X γ := by
      apply Units.ext
      apply Matrix.map_injective (inclInj_holds X)
      show ((matR (Subgroup.mem_inf.1 hg).1 : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map
          (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) =
        ((glOf X γ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map
          (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F))
      rw [← f1]
      rfl
    rw [e6, matE_glOf]
  exact Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)

end Stab

end Formalism.L2.SG.RhoPf
end
end

section

noncomputable section

open scoped Classical

open NumberField ValuativeRel IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.StabIntSh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem lg_int_of_locF (t : D.host.F)
    (h : ∀ p : PlF D, (D.s.atP p).ιE (algebraMap D.host.F D.host.E t) ∈ (D.s.atP p).O) :
    t ∈ (algebraMap (𝓞 D.host.F) D.host.F).range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one D.host.F t fun p => ?_
  have h1 := h p
  rw [(D.s.atP p).O_def, (D.s.atP p).compat] at h1
  have : Nontrivial (D.s.atP p).Ep := by
    have := (D.s.atP p).free
    exact Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)
  have h2 : IsIntegral 𝒪[(D.s.atP p).Fp] ((D.s.atP p).ιF t) :=
    (isIntegral_algebraMap_iff ).1 h1
  have h3 := (Valuation.integer.integers _).mem_of_integral h2
  have h4 : (D.s.atP p).ιF t ≤ᵥ (D.s.atP p).ιF 1 := by
    rw [map_one]
    exact (valuation (D.s.atP p).Fp).vle_one_iff.2 h3
  simpa using ((D.s.atP p).val t 1).1 h4

theorem lg_cj_mem (p : PlF D) {y : (D.s.atP p).Ep} (hy : y ∈ (D.s.atP p).O) :
    (D.s.atP p).cj y ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def] at hy ⊢
  exact hy.map ((D.s.atP p).cj.toAlgHom.restrictScalars 𝒪[(D.s.atP p).Fp])

theorem lg_iota_int (p : PlF D) (c : 𝓞 D.host.E) :
    (D.s.atP p).ιE (algebraMap (𝓞 D.host.E) D.host.E c) ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  have h1 : IsIntegral ℤ ((D.s.atP p).ιE (c : D.host.E)) :=
    (NumberField.RingOfIntegers.isIntegral_coe c).map (D.s.atP p).ιE.toIntAlgHom
  exact h1.tower_top

theorem lg_int_of_loc (z : D.host.E) (h : ∀ p : PlF D, (D.s.atP p).ιE z ∈ (D.s.atP p).O) : IsIntegral ℤ z := by
  have hfix : ∀ y : D.host.E, D.conjF y = y → (∀ p : PlF D, (D.s.atP p).ιE y ∈ (D.s.atP p).O) →
      IsIntegral ℤ y := by
    intro y hy hl
    obtain ⟨a, rfl⟩ := Formalism.MainNotions.BridgeLemma.conjF_fix y hy
    obtain ⟨b, rfl⟩ := lg_int_of_locF a hl
    exact (NumberField.RingOfIntegers.isIntegral_coe b).algebraMap
  have hc : ∀ p : PlF D, (D.s.atP p).ιE (D.conjF z) ∈ (D.s.atP p).O := fun p => by
    rw [← (D.s.atP p).cj_ιE]
    exact lg_cj_mem p (h p)
  have ht := hfix (z + D.conjF z) (by rw [map_add (f := _), Formalism.MainNotions.BridgeLemma.conjF_inv, add_comm])
    fun p => by rw [map_add]; exact add_mem (h p) (hc p)
  have hn := hfix (z * D.conjF z) (by rw [map_mul, Formalism.MainNotions.BridgeLemma.conjF_inv, mul_comm])
    fun p => by rw [map_mul]; exact mul_mem (h p) (hc p)
  have hz : IsIntegral (integralClosure ℤ D.host.E) z := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (⟨_, ht⟩ : integralClosure ℤ D.host.E) * Polynomial.X +
      Polynomial.C (⟨_, hn⟩ : integralClosure ℤ D.host.E), ?_, ?_⟩
    · monicity!
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      show z ^ 2 - (z + D.conjF z) * z + z * D.conjF z = 0
      ring
  exact isIntegral_trans z hz

theorem locGlob : LocGlob D := by
  intro I hI x
  constructor
  · intro h
    have key : ∀ y ∈ (I⁻¹ : FI D), x * y ∈ (1 : FI D) := by
      intro y hy
      rw [FractionalIdeal.mem_one_iff]
      refine ⟨⟨x * y, lg_int_of_loc _ fun p => ?_⟩, rfl⟩
      have hp := h p
      unfold LocMem at hp
      rw [map_mul]
      refine Submodule.span_induction
        (p := fun w _ => w * (D.s.atP p).ιE y ∈ (D.s.atP p).O) ?_ ?_ ?_ ?_ hp
      · rintro _ ⟨i, hi, rfl⟩
        rw [← map_mul]
        have hiy : i * y ∈ (1 : FI D) := by
          rw [← mul_inv_cancel₀ hI]
          exact FractionalIdeal.mul_mem_mul hi hy
        obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hiy
        rw [← hc]
        exact lg_iota_int p c
      · simp
      · intro a b _ _ ha hb
        rw [add_mul]
        exact add_mem ha hb
      · intro o a _ ha
        rw [smul_mul_assoc, Subring.smul_def]
        exact mul_mem o.2 ha
    have hle : FractionalIdeal.spanSingleton _ x * I⁻¹ ≤ 1 := by
      rw [FractionalIdeal.mul_le]
      intro i hi j hj
      obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ c (key j hj)
    rw [← FractionalIdeal.spanSingleton_le_iff_mem]
    calc FractionalIdeal.spanSingleton _ x = FractionalIdeal.spanSingleton _ x * I⁻¹ * I := by
          rw [mul_assoc, inv_mul_cancel₀ hI, mul_one]
      _ ≤ I := FractionalIdeal.mul_le.2 fun a ha b hb => by
          obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 (hle ha)
          rw [← Algebra.smul_def]
          exact Submodule.smul_mem _ c hb
  · intro hx p
    exact Submodule.subset_span ⟨x, hx, rfl⟩

theorem lg_ddS_ne : ddS D ≠ 0 := by
  rw [ddS, Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective]
  · exact differentIdeal_ne_bot
  · exact FaithfulSMul.algebraMap_injective _ _

theorem shapeNZ : ShapeNZ D := by
  have hd : ∀ k, ddPow D k ≠ 0 := fun k => zpow_ne_zero _ lg_ddS_ne
  refine ⟨hd, fun k => mul_ne_zero ?_ (hd k)⟩
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, qq]
  intro h0
  have hm : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ Ideal.span {((Lat.gS D : ℕ) : 𝓞 D.host.E)} :=
    Ideal.mem_span_singleton_self _
  rw [h0, Ideal.mem_bot] at hm
  exact (Formalism.MainNotions.LocalModelPeriodLattices.gS_pos D).ne' (by exact_mod_cast hm)

end Formalism.L2.SG.Pf.StabIntSh
end
end
