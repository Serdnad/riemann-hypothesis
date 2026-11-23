module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEigenvaluesClasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitNormBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1628
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

namespace GlobalTheory.MixHt.Uniq

variable {k : Type} [CommRing k]

theorem isometric_of_refines {X : Scheme.{0}} {p : X ⟶ Sp k} {N L : HermLB p} {π : N.B.ι → L.B.ι}
    (h : TwistTop.Refines N L π 0) : N.Isometric L :=
  HermLB.isometric_of_chart π h.le (fun x j j' hj hj' => h.g X (𝟙 X) x j j' hj hj')
    fun σ j y hy => ((h.φ σ j y hy).trans (add_zero _)).symm

theorem card_residueField {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) :
    Nat.card (X.residueField (i z)) = Nat.card (Z.residueField z) := by
  refine Nat.card_eq_of_bijective (i.residueFieldMap z) ⟨(i.residueFieldMap z).hom.injective, fun a => ?_⟩
  obtain ⟨b, rfl⟩ := Z.residue_surjective z a
  obtain ⟨c, rfl⟩ := i.stalkMap_surjective z b
  exact ⟨X.residue _ c, (ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i z) c :)⟩

end GlobalTheory.MixHt.Uniq


open GlobalTheory.MixHt.Uniq in
theorem GlobalTheory.MixHt.eq_of_isMix : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p →
    ∀ (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ p = q) (m m' : ℕ) T T', IsMix p m T → IsMix q m' T' →
    ∀ d : ℕ, d ≤ m → d ≤ m' → ∀ (L : Fin d → HermLB p) (L' : Fin d → HermLB q),
    (∀ a, ((L a).pull i hi).Isometric (L' a)) → ∀ y : Y, HasDim y d → T d L (i y) = T' d L' y := by
  intro k _ X Y p q hp i _ hi m m' T T' hT hT' d
  have hq : IsAmb q := hi ▸ hp.sub i
  have DX := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hp
  have DY := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q hq
  haveI : IsNoetherian Y := hq.isNoetherian
  induction d with
  | zero =>
    intro _ _ L L' _ y hy
    have hy' : HasDim (i y) 0 := (DX.2.2.2.2.1 Y i y 0).2 hy
    rw [hT.zero L (i y) hy', hT'.zero L' y hy, card_residueField i y]
  | succ e ih =>
    intro hm hm' L L' hL y hy
    have hW : IsAmb (cloι y ≫ q) := hq.sub (cloι y)
    have hgen : HasDim (genericPoint (clo y)) (e + 1) :=
      (DY.2.2.2.2.1 (clo y) (cloι y) (genericPoint (clo y)) (e + 1)).1 (by rw [cloι_genericPoint]; exact hy)
    have hdim : topologicalKrullDim (clo y) = ((e + 1 : ℕ) : WithBot ℕ∞) :=
      (DY.2.2.2.2.2 (clo y) (e + 1)).1 hgen
    obtain ⟨r, hr⟩ := exists_isRatSec ((L' 0).pull (cloι y) rfl).isLB
    have hij : (cloι y ≫ i) ≫ p = cloι y ≫ q := by rw [Category.assoc, hi]
    have hiso : ∀ (A : HermLB p) (A' : HermLB q), (A.pull i hi).Isometric A' →
        (A.pull (cloι y ≫ i) hij).Isometric (A'.pull (cloι y) rfl) := fun A A' h =>
      (isometric_of_refines (HermLB.refines_pull_pull A i hi (cloι y) rfl hij)).symm.trans (h.pull (cloι y) rfl)
    have h1 := hT'.recur (clo y) (cloι y ≫ q) (cloι y) rfl e hm' hdim (L' 0) (Fin.tail L')
      ((L' 0).pull (cloι y) rfl) (fun a => (L' a.succ).pull (cloι y) rfl) (HermLB.Isometric.refl _)
      (fun a => HermLB.Isometric.refl _) r hr
    have h2 := hT.recur (clo y) (cloι y ≫ q) (cloι y ≫ i) hij e hm hdim (L 0) (Fin.tail L)
      ((L' 0).pull (cloι y) rfl) (fun a => (L' a.succ).pull (cloι y) rfl) (hiso _ _ (hL 0))
      (fun a => hiso _ _ (hL a.succ)) r hr
    rw [Fin.cons_self_tail, cloι_genericPoint] at h1
    rw [Fin.cons_self_tail, Scheme.Hom.comp_apply, cloι_genericPoint] at h2
    rw [h1, h2]
    unfold recVal
    congr 1
    refine finsum_congr fun z => ?_
    by_cases hz : ((((L' 0).pull (cloι y) rfl)).div hr).mult z = 0
    · simp [hz]
    · have hz1 := CartierDiv.coheight_eq_one_of_mult_ne_zero hz
      have hzd : HasDim z e := ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k (clo y) (cloι y ≫ q) hW e hdim).1 z).1 hz1
      have hjz : HasDim (cloι y z) e := (DY.2.2.2.2.1 (clo y) (cloι y) z e).2 hzd
      dsimp only
      rw [Scheme.Hom.comp_apply, ih (by omega) (by omega) (Fin.tail L) (Fin.tail L') (fun a => hL a.succ) _ hjz]
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.PadicPolys

theorem minpoly_coeff_bdd : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ β : G.Cˣ, ∃ B : ℝ, ∀ (y : grp G β) (h : Gr G 1),
      f' (h⁻¹ * toP1 G β y * h) ≠ 0 → ∀ (φ : G.F →+* PadicAlgCl p) (k : ℕ),
        ‖φ ((minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k)‖ ≤ B := by
  intro p _ G K' f' hf β
  obtain ⟨k0, hk0⟩ := GlobalTheory.AtPBd.main p G 1 K' f' one_pos hf
  set R : ℝ := (p : ℝ) ^ k0 with hR
  have hR1 : 1 ≤ R := one_le_pow₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  refine ⟨max (R * R) 1 ^ (G.n ^ 2) * ((G.n ^ 2).choose (G.n ^ 2 / 2) : ℝ), ?_⟩
  intro y h hy φ k
  have hnrm : IsNrm G 1 (locC G (y : G.Cˣ × ℚˣ)) (h⁻¹ * toP1 G β y * h) h := by
    show nrmG (sigG G 1) 1 _ = _
    simp [nrmG]
    rfl
  obtain ⟨hs, -, hrt, hrti⟩ := hk0 (locC G (y : G.Cˣ × ℚˣ)) (h⁻¹ * toP1 G β y * h) h 1 hnrm (by simpa using hy)
  set yC : G.C := (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hyC
  have hint : IsIntegral G.F yC := Algebra.IsIntegral.isIntegral _
  have hmon : (minpoly G.F yC).Monic := minpoly.monic hint
  have hsn : ‖(((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p)‖ ≤ R := by
    rw [← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends]
    exact hs
  have hs0 : (((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p) ≠ 0 := by
    exact_mod_cast ((y : G.Cˣ × ℚˣ).2).ne_zero
  have hroot : ∀ μ ∈ ((minpoly G.F yC).map φ).roots, ‖μ‖ ≤ R * R := by
    intro μ hμ
    have hμ' : ((minpoly G.F yC).map φ).IsRoot μ := Polynomial.isRoot_of_mem_roots hμ
    rcases GlobalTheory.GlobEig.liesOver_or_conj G φ with hφ | hφ
    · obtain ⟨i, ν, hν, hνr⟩ := GlobalTheory.GlobEig.exists_root_rho G φ hφ yC μ hμ'
      rw [← hν]
      exact (hrt i ν hνr).trans (le_mul_of_one_le_left (by linarith) hR1)
    · have h2 := GlobalTheory.GlobEig.isRoot_minpoly_sh G yC φ μ hμ'
      obtain ⟨i, ν, hν, hνr⟩ := GlobalTheory.GlobEig.exists_root_rho G _ hφ (sh G yC) μ h2
      have h3 := GlobalTheory.GlobEig.isRoot_inv G i β (y : G.Cˣ × ℚˣ).1 (y : G.Cˣ × ℚˣ).2 y.2.1 ν hνr
      have h4 := hrti i _ h3
      rw [← hν]
      have e : ν = ν * (((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p)⁻¹ * (((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p) := by
        field_simp
      rw [e, norm_mul]
      exact mul_le_mul h4 hsn (norm_nonneg _) (by linarith)
  have hdeg : (minpoly G.F yC).natDegree ≤ G.n ^ 2 := G.rankC ▸ minpoly.natDegree_le yC
  rw [← Polynomial.coeff_map]
  exact Polynomial.coeff_bdd_of_roots_le φ hmon (IsAlgClosed.splits _) hdeg hroot k

end GlobalTheory.LKCx.PadicPolys
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.FinClsLoc

variable {p : ℕ} [Fact p.Prime]

theorem glueL_evalT_inC (G : HTGroup p) (w : AwayP p) (c : G.C) :
    Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (inC G (AfP p) c) =
      inC G (w.1.adicCompletion ℚ) c := by
  show Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) ((1 : AfP p) ⊗ₜ c) = (1 : w.1.adicCompletion ℚ) ⊗ₜ c
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

theorem glueL_evalT_starT (G : HTGroup p) (w : AwayP p) (a : AfP p ⊗[ℚ] G.C) :
    Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (starT G.star (AfP p) a).unop =
      (starT G.star (w.1.adicCompletion ℚ) (Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) a)).unop := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r y => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, starT_tmul]
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]

theorem glueL_evalT_algebraMap (G : HTGroup p) (w : AwayP p) (t : AfP p) :
    Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) t) =
      algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (AfP.eval w t) := by
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem glueL_compL_toAfF_fst (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) (w : AwayP p) :
    ((((compL G w (toAfF G β x t hx y) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) :
        w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (x : AfP p ⊗[ℚ] G.C) *
        inC G (w.1.adicCompletion ℚ) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) *
        Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := by
  show Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) ((x : AfP p ⊗[ℚ] G.C) *
    inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) = _
  rw [map_mul, map_mul, glueL_evalT_inC]

theorem glueL_sh_inv_mul (G : HTGroup p) (c : G.Cˣ) : sh G ((c⁻¹ : G.Cˣ) : G.C) * sh G (c : G.C) = 1 := by
  simp only [sh]
  rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]

theorem glueL_main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) (g : G.GAf) (c Y : G.Cˣ),
    (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * Y * ((c⁻¹ : G.Cˣ) : G.C) → ∀ w : AwayP p,
    ∃ (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) (lam : (w.1.adicCompletion ℚ)ˣ),
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (Y : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = ((((compL G w (g⁻¹ * toAfF G β x t hx y * g) : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) ((Y⁻¹ : G.Cˣ) : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = (((((compL G w (g⁻¹ * toAfF G β x t hx y * g) : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ)⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * (inC G (w.1.adicCompletion ℚ) (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
        inC G (w.1.adicCompletion ℚ) (β : G.C)) * (starT G.star (w.1.adicCompletion ℚ) (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop = algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (lam : w.1.adicCompletion ℚ) := by
  intro p _ G β x t hx y g c Y hy w
  let φ := Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C)
  let u : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ :=
    ((compL G w g : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1
  let ν : (w.1.adicCompletion ℚ)ˣ :=
    ((compL G w g : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).2
  let xw : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (φ : AfP p ⊗[ℚ] G.C →* w.1.adicCompletion ℚ ⊗[ℚ] G.C) x
  let ci : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom c
  let mY : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom Y
  let tw : (w.1.adicCompletion ℚ)ˣ := Units.map (AfP.eval w : AfP p →* w.1.adicCompletion ℚ) t
  have hT : ((compL G w (toAfF G β x t hx y) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 = xw * (ci * mY * ci⁻¹) * xw⁻¹ := by
    apply Units.ext
    rw [glueL_compL_toAfF_fst]
    have hy' : ((y : G.Cˣ × ℚˣ).1 : G.Cˣ) = c * Y * c⁻¹ := Units.ext (by rw [hy]; rfl)
    rw [hy', ← map_inv, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have E : ((compL G w (g⁻¹ * toAfF G β x t hx y * g) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 = (u⁻¹ * xw * ci) * mY * (u⁻¹ * xw * ci)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    change u⁻¹ * ((compL G w (toAfF G β x t hx y) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 * u = _
    rw [hT]
    group
  refine ⟨u⁻¹ * xw * ci, tw * ν⁻¹, ?_, ?_, ?_⟩
  · rw [E]; rfl
  · rw [E, show (u⁻¹ * xw * ci * mY * (u⁻¹ * xw * ci)⁻¹)⁻¹ = (u⁻¹ * xw * ci) * mY⁻¹ * (u⁻¹ * xw * ci)⁻¹ by group]
    rfl
  · have hu : ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
        (starT G.star (w.1.adicCompletion ℚ) ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C)).unop =
        algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) ((ν⁻¹ : (w.1.adicCompletion ℚ)ˣ) : w.1.adicCompletion ℚ) :=
      ((compL G w g)⁻¹).2
    have hxw : φ (x : AfP p ⊗[ℚ] G.C) * inC G (w.1.adicCompletion ℚ) (β : G.C) *
        (starT G.star (w.1.adicCompletion ℚ) (φ (x : AfP p ⊗[ℚ] G.C))).unop =
        algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (tw : w.1.adicCompletion ℚ) := by
      have h := congrArg φ hx
      rw [map_mul, map_mul, glueL_evalT_inC, glueL_evalT_starT, glueL_evalT_algebraMap] at h
      exact h
    have hs : ∀ z : G.C, (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) z)).unop =
        inC G (w.1.adicCompletion ℚ) (sh G z) := fun z => starT_tmul G.star _ 1 z
    have hC : (c : G.C) * (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * β *
        sh G (c : G.C) = β := by
      calc (c : G.C) * (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * β *
            sh G (c : G.C)
          = ((c : G.C) * ((c⁻¹ : G.Cˣ) : G.C)) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) *
              (((β⁻¹ : G.Cˣ) : G.C) * β) * sh G (c : G.C) := by simp only [mul_assoc]
        _ = β * (sh G ((c⁻¹ : G.Cˣ) : G.C) * sh G (c : G.C)) := by
            rw [Units.mul_inv, Units.inv_mul, one_mul, mul_one, mul_assoc]
        _ = β := by rw [glueL_sh_inv_mul, mul_one]
    have hk : (((u⁻¹ * xw * ci : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ)) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
        ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) * φ (x : AfP p ⊗[ℚ] G.C) *
          inC G (w.1.adicCompletion ℚ) (c : G.C) := rfl
    rw [hk, RingHom.map_mul (starT G.star (w.1.adicCompletion ℚ)), RingHom.map_mul (starT G.star (w.1.adicCompletion ℚ)),
      MulOpposite.unop_mul, MulOpposite.unop_mul, hs]
    calc _ = ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
          (φ (x : AfP p ⊗[ℚ] G.C) * (inC G (w.1.adicCompletion ℚ) ((c : G.C) *
            (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * β * sh G (c : G.C))) *
          (starT G.star (w.1.adicCompletion ℚ) (φ (x : AfP p ⊗[ℚ] G.C))).unop) *
          (starT G.star (w.1.adicCompletion ℚ) ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C)).unop := by
          simp only [map_mul, mul_assoc]
      _ = algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (tw : w.1.adicCompletion ℚ) *
          (((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
          (starT G.star (w.1.adicCompletion ℚ) ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C)).unop) := by
          rw [hC, hxw, ← mul_assoc, ← Algebra.commutes, mul_assoc]
      _ = _ := by rw [hu, ← map_mul, Units.val_mul]

end GlobalTheory.FinClsLoc
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.AtP

theorem den_factorization_le {p : ℕ} (hp : p.Prime) (q : ℚ) (e : ℕ) (k : ℤ) (m : ℕ) (hm : ¬ p ∣ m)
    (h : q * (p : ℚ) ^ e = k / m) : q.den.factorization p ≤ e := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hm0' : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
  have hq : q = Rat.divInt k ((m * p ^ e : ℕ) : ℤ) := by
    rw [Rat.divInt_eq_div]
    push_cast
    have hp0 : (p : ℚ) ^ e ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
    rw [eq_div_iff (mul_ne_zero hm0' hp0), mul_comm (m : ℚ), ← mul_assoc, h, div_mul_cancel₀ _ hm0']
  have hd : q.den ∣ m * p ^ e := by
    have := Rat.den_dvd k ((m * p ^ e : ℕ) : ℤ)
    rw [← hq] at this
    exact_mod_cast this
  have hne : m * p ^ e ≠ 0 := mul_ne_zero hm0 (pow_ne_zero _ hp.ne_zero)
  have := (Nat.factorization_le_iff_dvd (Rat.den_nz q) hne).2 hd p
  rw [Nat.factorization_mul hm0 (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hm, hp.factorization_pow, Finsupp.single_eq_same, zero_add] at this
  exact this

end GlobalTheory.AtP

namespace GlobalTheory.AtP

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (h₂ : Gr G 1), ∃ k : ℕ, ∀ y : grp G β, f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 → (∀ i, ((Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i).den.factorization p ≤ k) ∧ (((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)).den.factorization p ≤ k := by
  intro p _ G β K' f' hf h₂
  have hp : p.Prime := Fact.out
  obtain ⟨B, e₁, hB⟩ := GlobalTheory.T.regular_elements_bounded_padic p G K' f' hf β h₂
  obtain ⟨e₂, he⟩ := GlobalTheory.T.bounded_coordinates_p_power_denominator p G B
  refine ⟨max e₁ e₂, fun y hy => ?_⟩
  obtain ⟨hb, k, m, hm, hs⟩ := hB y hy
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨k', m', hm', hc⟩ := he _ hb i
    exact (den_factorization_le hp _ e₂ k' m' hm' hc).trans (le_max_right _ _)
  · rw [Units.val_inv_eq_inv_val]
    exact (den_factorization_le hp _ e₁ k m hm hs).trans (le_max_left _ _)

end GlobalTheory.AtP
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm

theorem algHom_aeval_ev {m m' : ℕ} {ι : Type} (φ : Alt m →ₐ[ℂ] Alt m') (u : ι → Ev m) (u' : ι → Ev m')
    (h : ∀ i, φ (u i : Alt m) = (u' i : Alt m')) (P : MvPolynomial ι ℝ) :
    φ ((aeval u (P.map (algebraMap ℝ ℂ)) : Ev m) : Alt m) = ((aeval u' (P.map (algebraMap ℝ ℂ)) : Ev m') : Alt m') := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.map_C, MvPolynomial.aeval_C]
    exact φ.commutes _
  | add p q hp hq =>
    simp only [map_add (f := _), Subalgebra.coe_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, Subalgebra.coe_mul, hp, h]

theorem pullback_evalF : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n') (g : M' → M) (ι : Type) (w : ι → A.Pt → Ev n) (w' : ι → A'.Pt → Ev n'), (∀ i, A.pullback A' g (fld A (w i)) = fld A' (w' i)) → ∀ P : MvPolynomial ι ℝ, A.pullback A' g (evalF A w P) = evalF A' w' P := by
  intro M M' _ _ n n' A A' g ι w w' hw P
  funext x
  exact algHom_aeval_ev _ _ _ (fun i => congrFun (hw i) x) P

end GlobalTheory.LineForm
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unitaryHeckeCharCM_infinityComponent_globalUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ k : Eˣ, ((μ.inf k : ℂˣ) : ℂ) = ∏ v : InfinitePlace E, (v.embedding (k : E) / (‖v.embedding (k : E)‖ : ℂ)) ^ e v := by
  first | exact @GlobalTheory.BCT.inf_mu_unit | exact GlobalTheory.BCT.inf_mu_unit | (intros; apply GlobalTheory.BCT.inf_mu_unit <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_finite_level_sum : ∀ (H : Type) [Group H] (K L : Subgroup H) (u : H → ℂ), L ≤ K → L ≤ rStab u → L.relIndex K ≠ 0 → hint K u = ((L.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ L, u q.out := by
  first | exact @GlobalTheory.BCT.HintLevel.hint_level | exact GlobalTheory.BCT.HintLevel.hint_level | (intros; apply GlobalTheory.BCT.HintLevel.hint_level <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_integral_div : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ → ∀ (Λ : AddSubgroup V), IsOpen (Λ : Set V) → IsCompact (Λ : Set V) → ∀ u : V → ℂ, (∃ U : AddSubgroup V, IsOpen (U : Set V) ∧ ∀ x, ∀ y ∈ U, u (x + y) = u x) → HasCompactSupport u → GlobalTheory.BCT.hint (AddSubgroup.toSubgroup Λ) (fun X : Multiplicative V => u (Multiplicative.toAdd X)) = ((μ (Λ : Set V)).toReal : ℂ)⁻¹ * ∫ x, u x ∂μ := by
  first | exact @GlobalTheory.HaarSum.hint_eq_integral | exact GlobalTheory.HaarSum.hint_eq_integral | (intros; apply GlobalTheory.HaarSum.hint_eq_integral <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.heckeOperator_testFamily_preserves_level_forms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ v ∈ π ⊓ fixed (RF E n) (globLev S K'), hop S K' f v ∈ π ⊓ fixed (RF E n) (globLev S K') := by
  first | exact @GlobalTheory.BCT.hop_mem_inf_fixed | exact GlobalTheory.BCT.hop_mem_inf_fixed | (intros; apply GlobalTheory.BCT.hop_mem_inf_fixed <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.localComponent_definiteUnitaryFinitePart_eq_localPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (γ : UE E n) (w : Pl E), toSub (UL n w) (cLoc w ((finPt γ : finU (E := E) (n := n)) : UA E n)) = locPt w γ := by
  first | exact @GlobalTheory.BCT.locPt_finPt | exact GlobalTheory.BCT.locPt_finPt | (intros; apply GlobalTheory.BCT.locPt_finPt <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.localTestFactor_ne_zero_of_globalProduct_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), IsTest (KL n) K' f → ∀ y : finU (E := E) (n := n), (∀ᶠ w in cofinite, cLoc w y.1 ∈ GlobalTheory.LFun.KGL w (n := n)) → globFn S f y ≠ 0 → ∀ w ∈ S, f w (toSub _ (cLoc w y.1)) ≠ 0 := by
  first | exact @GlobalTheory.BCT.SuppFin.factor_ne_zero_of_globFn_ne_zero | exact GlobalTheory.BCT.SuppFin.factor_ne_zero_of_globFn_ne_zero | (intros; apply GlobalTheory.BCT.SuppFin.factor_ne_zero_of_globFn_ne_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.continuous_unitaryLocalComponent_toLocalUnitaryGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ w : Pl E, Continuous (fun x : finU (E := E) (n := n) => toSub (UL n w) (cLoc w (x : UA E n))) := by
  first | exact @GlobalTheory.BCT.toSub_cLoc_fin_continuous | exact GlobalTheory.BCT.toSub_cLoc_fin_continuous | (intros; apply GlobalTheory.BCT.toSub_cLoc_fin_continuous <;> assumption)
end
