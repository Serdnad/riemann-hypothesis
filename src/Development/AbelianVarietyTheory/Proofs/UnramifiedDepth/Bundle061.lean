module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle039
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle058
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle040
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle049
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle060
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle039
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle059
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicUnitQuotientPrincipalBasis
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawSelfConjugateSquar
import Formalism.LocalToGlobal.CharacterGerms.Bundle007
public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GoodCurvesPairingMemMaxIdeal
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeAdjointEndPairElementaryBlock
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointTeichmullerEndSelfConjugatePlace
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.DualLattices.Bundle007
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.DualLattices.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

@[expose] public section

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.goodCurves_pairing_mem_maxIdeal : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ (H : ∀ g, X.CartHyp V g) (g : Fin 2) (a a' : ZMod d) (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C) (w' : I (1 - g) → C) (x' : ℕ → I (1 - g) ⊕ JJ I (1 - g) → C), (RawChart.cart (H g)).Good a w x → (RawChart.cart (H (1 - g))).Good a' w' x' → (∀ c, V.MM ((RawChart.cart (H g)).V2 x c)) → V.MM (∑ q : I (1 - g), (RawChart.cart (H g)).c0' x q * w' q) := by
  first | exact @GlobalTheory.RowLaw.good_pairing_mem_max | exact GlobalTheory.RowLaw.good_pairing_mem_max | (intros; apply GlobalTheory.RowLaw.good_pairing_mem_max <;> assumption)
end

section

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ChF

theorem iRel_succ : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G) (k : ℕ) (S : Type) [CommRing S] [Algebra R S] χ z, IRel (U.gt k) S χ z → IRel (U.gt (k + 1)) S χ z := by
  rintro R _ _ I D A G _ _ U k S _ _ χ z ⟨w, hw, hz⟩
  have t : Out.thickMap R I k G ≫ (Out.fstG I (k + 1) G).left = (Out.fstG I k G).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  let Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) :=
    Over.mk (w ≫ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.toPre.X).hom)
  let τ : Z ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.toPre.X := Over.homMk w rfl
  let r : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k G).left := (τ ≫ (U.gt k).i).left
  have hr : r ≫ (Out.fstG I k G).left = z.left := (Category.assoc _ _ _).trans hz
  have c : r ≫ (U.gt k).pG.left = r ≫ (Out.fstG I k G).left ≫ G.hom ≫ eSec D.toPre.P.A :=
    (CharAgree.comp_q_eq_one_iff (U.gt k) (τ ≫ (U.gt k).i)).1 (by
      rw [Category.assoc, (U.gt k).isKernel.w, ← Category.assoc]
      exact congrArg (· ≫ _) (toUnit_unique _ _))
  let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (k + 1 + 1)))) :=
    Over.mk ((r ≫ Out.thickMap R I k G) ≫ (Out.thickObj R I (k + 1) G).hom)
  let a : Z' ⟶ Out.thickObj R I (k + 1) G := Over.homMk (r ≫ Out.thickMap R I k G) rfl
  have c' : a.left ≫ (U.gt (k + 1)).pG.left =
      a.left ≫ (Out.fstG I (k + 1) G).left ≫ G.hom ≫ eSec D.toPre.P.A := by
    refine (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (U.gt_q k)).trans (c.trans ?_))
    refine Eq.trans (congrArg (r ≫ ·) ?_) (Category.assoc _ _ _).symm
    exact (congrArg (· ≫ G.hom ≫ eSec D.toPre.P.A) t.symm).trans (Category.assoc _ _ _)
  let τ' := (U.gt (k + 1)).isKernel.lift a (toUnit _) ((CharAgree.comp_q_eq_one_iff (U.gt (k + 1)) a).2 c')
  have hτ : τ' ≫ (U.gt (k + 1)).i = a := (U.gt (k + 1)).isKernel.lift_fst _ _ _
  refine ⟨τ'.left, fun x => ?_, ?_⟩
  · refine Eq.trans (congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ?_) (hw x)
    apply TopCat.Presheaf.section_ext (Spec (CommRingCat.of S)).sheaf ⊤
    intro y hy
    choose J hJ using fun ψ : Spec (CommRingCat.of S) ⟶ D.toPre.P.A.left =>
      Geo.Tor.exists_chart D.toPre.P.isLB (ψ y)
    have k₀ := (TorusCoord.val_torus_point_and_translate R I D.toPre k G (U.gt k) Z τ 1 y J hJ x).1
    have k₁ := (TorusCoord.val_torus_point_and_translate R I D.toPre (k + 1) G (U.gt (k + 1)) Z' τ' 1 y J hJ x).1
    rw [hτ] at k₁
    have e := congrArg Units.val (k₁.symm.trans ((Geo.Tor.val_pull hJ _ (Out.thickMap R I k G) r).symm.trans
      ((Geo.Tor.val_corr hJ (U.gt_t k x) r).trans k₀)))
    exact (Geo.Tor.gm_val _ _ ⊤ trivial _).symm.trans (e.trans (Geo.Tor.gm_val _ _ ⊤ trivial _))
  · refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun φ => φ.left ≫ (Out.fstG I (k + 1) G).left) hτ).trans ?_
    exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) t).trans hr)

end GlobalTheory.ChF
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem lav_fp {O : Type} [CommRing O] {J : Type} [Fintype J]
    (h : ∀ (n : ℕ) (M N : Submodule O (Fin n → O)), M.FG → N.FG → N ≤ M →
      Module.FinitePresentation O (M ⧸ N.comap M.subtype))
    (M N : Submodule O (J → O)) (hM : M.FG) (hN : N.FG) (hle : N ≤ M) :
    Module.FinitePresentation O (M ⧸ N.comap M.subtype) := by
  let e : (J → O) ≃ₗ[O] (Fin (Fintype.card J) → O) :=
    LinearEquiv.funCongrLeft O O (Fintype.equivFin J).symm
  have h1 := h _ (M.map e.toLinearMap) (N.map e.toLinearMap) (hM.map _) (hN.map _)
    (Submodule.map_mono hle)
  refine Module.FinitePresentation.of_equiv
    (Submodule.Quotient.equiv ((N.map e.toLinearMap).comap (M.map e.toLinearMap).subtype) (N.comap M.subtype)
      (e.submoduleMap M).symm ?_)
  ext x
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨y, ⟨z, hz, hzy⟩, rfl⟩
    have : (((e.submoduleMap M).symm y : M) : J → O) = z := by
      rw [LinearEquiv.submoduleMap_symm_apply, ← hzy]
      exact e.symm_apply_apply z
    exact this ▸ hz
  · intro hx
    exact ⟨e.submoduleMap M x, ⟨x, hx, rfl⟩, (e.submoduleMap M).symm_apply_apply x⟩

private theorem lav_num (P D c cw X : ℝ) (n rm vd q : ℝ) (rp rm' h : ℕ) (hrm : rm = rm')
    (hP0 : 0 < P) (hP1 : P ≤ 1) (hvd : 0 ≤ n * vd) (hD : D = P ^ (n * vd)) (hh : h ≤ rp + rm')
    (hcw : P ^ ((n * rm) / q) ≤ cw) (hc : cw ≤ c) (hX : 0 ≤ X)
    (hl : c ^ 2 * D ^ h ≤ X ^ 2 * D ^ rp) : P ^ (n * rm * (1 / q + vd / 2)) ≤ X := by
  have hD0 : 0 < D := hD ▸ Real.rpow_pos_of_pos hP0 _
  have hD1 : D ≤ 1 := hD ▸ Real.rpow_le_one hP0.le hP1 hvd
  have h0 : 0 < P ^ ((n * rm) / q) := Real.rpow_pos_of_pos hP0 _
  have h1 : D ^ (rp + rm') ≤ D ^ h := pow_le_pow_of_le_one hD0.le hD1 hh
  have h2 : c ^ 2 * D ^ rm' ≤ X ^ 2 := by
    have : c ^ 2 * D ^ rm' * D ^ rp ≤ X ^ 2 * D ^ rp := by
      calc c ^ 2 * D ^ rm' * D ^ rp = c ^ 2 * D ^ (rp + rm') := by ring
        _ ≤ c ^ 2 * D ^ h := mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
        _ ≤ _ := hl
    exact le_of_mul_le_mul_right this (pow_pos hD0 _)
  have h3 : (P ^ (n * rm * (1 / q + vd / 2))) ^ 2 = (P ^ ((n * rm) / q)) ^ 2 * D ^ rm' := by
    rw [hD, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hP0.le,
      ← Real.rpow_mul hP0.le, ← Real.rpow_mul hP0.le, ← Real.rpow_add hP0, ← hrm]
    congr 1
    push_cast
    ring
  refine (pow_le_pow_iff_left₀ (Real.rpow_pos_of_pos hP0 _).le hX two_ne_zero).1 ?_
  rw [h3]
  refine le_trans ?_ h2
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0.le (hcw.trans hc) 2) (pow_pos hD0 _).le

theorem colength_bound_linDat : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (vd : ℝ), HasVd p v w t vd → ∀ (rp rm : ℕ) (W : Fin w.n → Fin rp → Fin d → O), (∀ j, EigB ρG ((t j : Emb (O := O) w.e) : OE →+* O) (W j)) → (∀ τ ∈ Emb (O := O) w.bar, ∃ W' : Fin rm → Fin d → O, EigB ρG τ W') → ∃ xs : Fin w.n → NNReal, (∀ j, HasLen v O ((Fin rp → O) ⧸ Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W j) (s k))) (xs j)) ∧ v (algebraMap O C (p : O)) ^ ((w.n : ℝ) * rm * (1 / ((p : ℝ) - 1) + vd / 2)) ≤ ∏ j, xs j := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hU g H d r m A B ρG N s hL w t vd hvd rp rm W hW hW'
  have hp0 : 0 < v (algebraMap O C (p : O)) := by
    rw [map_natCast, zero_lt_iff, Ne, map_eq_zero]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : v (algebraMap O C (p : O)) < 1 :=
    lt_of_le_of_ne (hv.map_le_one _) fun h =>
      (Fact.out : ¬IsUnit (p : O)) (hv.isUnit_iff_valuation_eq_one.2 h)
  obtain ⟨-, -, α, b, hb⟩ := GlobalTheory.PlaceMono.place_monogenic p OE ⟨w.e, w.idem, w.ne_zero, w.prim⟩
  have hrm : ∀ τ ∈ Emb (O := O) w.bar,
      eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp τ) ≤ rm := by
    intro τ hτ
    obtain ⟨W', hW''⟩ := hW' τ hτ
    have h1 := (GlobalTheory.ChF.eigB_res_surjective C v O hv OE d rm ρG τ W' hW'').2.2
    have h2 := (GlobalTheory.T.eigenspaceDim_add_split_exact_transpose C O OE d r g A B hL.exact ρG
      ((RingHom.mapMatrix (Int.castRingHom O)).comp N)
      (H.ρL.comp (Algebra.TensorProduct.includeRight : OE →ₐ[ℤ] ℤ_[p] ⊗[ℤ] OE).toRingHom)
      hL.eqB hL.eqA ((algebraMap O C).comp τ)).1
    rw [h1] at h2
    exact le_of_le_of_eq (Nat.le_add_left _ _) h2.symm
  obtain ⟨cw, hcw, hcwb⟩ := GlobalTheory.T.abelianPart_cokernel_length_le p C v O hv OE cp hU g H hL.noPad.1 hL.noPad.2 w t rm hrm
  obtain ⟨h, ψ, hh, hψ, f, hf⟩ := GlobalTheory.T.exists_abelian_torus_generators_at_place p C v O hv OE cp hU g H d r m A B ρG N s hL w t α b hb rp rm W hW hrm
  obtain ⟨hinj, hvd0, hD⟩ := GlobalTheory.PowerBasisDiscr.discr_power_basis p C v O hv OE w t vd hvd α b hb
  obtain ⟨hex, hmono, hfp⟩ := GlobalTheory.ChF.hasLen_exists_mono_fp C v O hv
  have hres := fun j => GlobalTheory.ChF.eigB_res_surjective C v O hv OE d rp ρG _ (W j) (hW j)
  have hstab : ∀ (x : ℤ_[p] ⊗[ℤ] OE) (u : Fin d → O), ∃ u' : Fin d → O, ∀ j,
      Pdiv.ChartF.res (W j) u' = tauExt ((t j : Emb (O := O) w.e) : OE →+* O) x • Pdiv.ChartF.res (W j) u := by
    intro x u
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, fun j => by simp⟩
    | tmul c a =>
      refine ⟨algebraMap ℤ_[p] O c • ((ρG a)ᵀ *ᵥ u), fun j => ?_⟩
      rw [map_smul, (hres j).2.1, smul_smul]
      simp [tauExt, Algebra.ofId_apply]
    | add x y hx hy =>
      obtain ⟨u1, h1⟩ := hx
      obtain ⟨u2, h2⟩ := hy
      exact ⟨u1 + u2, fun j => by rw [map_add (f := _), h1, h2, map_add (f := _), add_smul]⟩
  let κ : (Fin d → O) →ₗ[O] (Fin w.n × Fin rp → O) :=
    LinearMap.pi fun y : Fin w.n × Fin rp => (LinearMap.proj y.2).comp (Pdiv.ChartF.res (W y.1))
  have hκa : ∀ u y, κ u y = Pdiv.ChartF.res (W y.1) u y.2 := fun u y => rfl
  have hMfg : (LinearMap.range κ).FG := by
    rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _
  have hmem : ∀ (x : ℤ_[p] ⊗[ℤ] OE) (u : Fin d → O), (fun y : Fin w.n × Fin rp =>
      tauExt ((t y.1 : Emb (O := O) w.e) : OE →+* O) x * κ u y) ∈ LinearMap.range κ := by
    intro x u
    obtain ⟨u', hu'⟩ := hstab x u
    refine ⟨u', funext fun y => ?_⟩
    rw [hκa, hκa, hu']
    rfl
  obtain ⟨c, hc⟩ := hex _ (lav_fp hfp (LinearMap.range κ)
    (Submodule.span O (Set.range fun q : Fin w.n × Fin h => fun y : Fin w.n × Fin rp =>
      tauExt ((t y.1 : Emb (O := O) w.e) : OE →+* O) α ^ (q.1 : ℕ) * Pdiv.ChartF.res (W y.1) (ψ q.2) y.2))
    hMfg (Submodule.fg_span (Set.finite_range _)) (by
      rw [Submodule.span_le]
      rintro _ ⟨q, rfl⟩
      have := hmem (α ^ (q.1 : ℕ)) (ψ q.2)
      simp only [map_pow] at this
      exact this))
  have hcc : cw ≤ c := hmono _ _ f cw c hf hcw hc
  have hcw0 : (0 : ℝ) < cw := lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hp0) _) hcwb
  have hc0 : c ≠ 0 := (lt_of_lt_of_le (by exact_mod_cast hcw0) hcc : (0 : NNReal) < c).ne'
  obtain ⟨x, hx, hineq⟩ := GlobalTheory.T.lattice_inequality_valuation_integers C v O hv ⟨_, hp0, hp1⟩ w.n rp h
    (fun j => tauExt ((t j : Emb (O := O) w.e) : OE →+* O) α) hinj (LinearMap.range κ) hMfg
    (by rintro _ ⟨u, rfl⟩; exact hmem α u)
    (by
      intro τ z
      obtain ⟨u, hu⟩ := (hres τ).1 z
      exact ⟨κ u, ⟨u, rfl⟩, fun i => by rw [hκa, hu]⟩)
    (fun l => κ (ψ l)) (fun l => ⟨ψ l, rfl⟩) c hc0 hc
  have hxs : ∀ j, ∃ y, HasLen v O ((Fin rp → O) ⧸ Submodule.span O
      (Set.range fun k => Pdiv.ChartF.res (W j) (s k))) y ∧ x j ≤ y := by
    intro j
    have hle : Submodule.span O (Set.range fun l => fun i => κ (ψ l) (j, i)) ≤
        Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W j) (s k)) := by
      rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact hψ l j
    obtain ⟨y, hy⟩ := hex ((Fin rp → O) ⧸ Submodule.span O
      (Set.range fun k => Pdiv.ChartF.res (W j) (s k)))
      (Module.finitePresentation_of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
        (by rw [Submodule.ker_mkQ]; exact Submodule.fg_span (Set.finite_range _)))
    exact ⟨y, hy, hmono _ _ (Submodule.factor hle) _ _ (Submodule.factor_surjective hle) (hx j) hy⟩
  choose xs hxs1 hxs2 using hxs
  refine ⟨xs, hxs1, le_trans ?_ (Finset.prod_le_prod' fun j _ => hxs2 j)⟩
  rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
  refine lav_num _ _ c cw _ _ _ _ _ rp rm h rfl (by exact_mod_cast hp0) (by exact_mod_cast hp1.le) hvd0 hD hh
    hcwb (by exact_mod_cast hcc) (NNReal.coe_nonneg _) ?_
  exact_mod_cast hineq

end GlobalTheory.ChF
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_formalTorus_character_lift_to_law : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d r : ℕ) (F : FGLaw O d), FH p F.F → ∀ (J : Fin d → PS O 1 r) (A' : Matrix (Fin r) (Fin d) O), IsHomF (gmF O r) F.F J → A' * lin J = 1 → ∀ i : Fin r, ∃ u : PS O 1 d, IsCh F.F u ∧ (lin J)ᵀ *ᵥ dl u = Pi.single i 1 := by
  first | exact @GlobalTheory.ChF.Lift.exists_char_lift | exact GlobalTheory.ChF.Lift.exists_char_lift | (intros; apply GlobalTheory.ChF.Lift.exists_char_lift <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open MvPowerSeries Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowLawSquare ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLawPair

variable {C : Type} [Field C] {dd : ℕ} {τ : Type}

theorem subst_oneVarGerm_eq_substPointsPowerSeries {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) (f : PS C 1 dd) :
    subst a (un1 f) = sb ![a] f := by
  rw [GlobalTheory.RowLawSquare.subst_singlePointUncurry ha]
  unfold sb
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  rfl

theorem oneVarGerm_eq_substPoints_X (f : PS C 1 dd) : un1 f = sb ![(X : Fin dd → MvPowerSeries (Fin dd) C)] f := by
  rw [← subst_oneVarGerm_eq_substPointsPowerSeries (fun _ => constantCoeff_X _), subst_self]
  rfl

theorem zc_gp {n : ℕ} (j : Fin n) : Zc (gp C (Fin dd) j) := fun _ => constantCoeff_X _

theorem intS_gp (V : VF C) {n : ℕ} (j : Fin n) (i : Fin dd) : IntS V (gp C (Fin dd) j i) := intS_X V _

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd)
  {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I)

theorem formalAdd_eq_law {a b : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) :
    addP (Y.raw p) a b = law Y a b := by
  funext i
  show subst (fun x => subst a (un1 (Y.lg x)) + subst b (un1 (Y.lg x))) (un1 (Y.ex i)) = _
  simp only [subst_oneVarGerm_eq_substPointsPowerSeries ha, subst_oneVarGerm_eq_substPointsPowerSeries hb, lg_law Y ha hb]
  rw [subst_oneVarGerm_eq_substPointsPowerSeries (fun x => cc_sb (zc1 (zc_law Y ha hb)) (zc_lg Y x)), ex_lg Y (zc_law Y ha hb)]

theorem hAt_eq_sb (a b : Fin dd → MvPowerSeries τ C) : hAt (Y.raw p) a b = sb ![a, b] Y.h := by
  show subst _ Y.h = subst _ Y.h
  congr 1
  funext ⟨s, x⟩
  fin_cases s <;> rfl

theorem cc_sb_h {a b : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) :
    constantCoeff (sb ![a, b] Y.h) = 0 :=
  cc_sb (zc2 ha hb) (cc_h Y)

theorem sb_gp_self (f : PS C 2 dd) : sb ![gp C (Fin dd) (0 : Fin 2), gp C (Fin dd) 1] f = f := by
  have e : (fun q : Fin 2 × Fin dd => ![gp C (Fin dd) (0 : Fin 2), gp C (Fin dd) 1] q.1 q.2) = X := by
    funext ⟨s, x⟩
    fin_cases s <;> rfl
  unfold sb
  rw [e, subst_self]
  rfl

theorem rLaw_raw : RLaw (Y.raw p) V := {
  charZero := inferInstance
  closed := Y.algClosed
  odd := Y.l_odd
  lin := fun i μ hμ => by
    classical
    show coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.lg i) = _
    rw [Y.lg_lin i _ (by rwa [Finsupp.degree_mapDomain]), coeff_X, coeff_X]
    have hinj : Function.Injective fun x : Fin dd => ((0 : Fin 1), x) := fun _ _ h => congrArg Prod.snd h
    refine if_congr ?_ rfl rfl
    rw [← (Finsupp.mapDomain_injective (M := ℕ) hinj).eq_iff (a := μ), Finsupp.mapDomain_single]
  exc := fun i => (constantCoeff_uncurry _).trans (Y.ex_const i)
  lgex := fun i => by
    show subst (fun x => un1 (Y.ex x)) (un1 (Y.lg i)) = _
    rw [subst_oneVarGerm_eq_substPointsPowerSeries (fun x => (constantCoeff_uncurry _).trans (Y.ex_const x))]
    simp only [oneVarGerm_eq_substPoints_X]
    exact lg_ex Y (fun _ => constantCoeff_X _) i
  exlg := fun i => by
    show subst (fun x => un1 (Y.lg x)) (un1 (Y.ex i)) = _
    rw [subst_oneVarGerm_eq_substPointsPowerSeries (fun x => (constantCoeff_uncurry _).trans (zc_lg Y x))]
    simp only [oneVarGerm_eq_substPoints_X]
    exact ex_lg Y (fun _ => constantCoeff_X _) i
  axes := h_axes Y
  addInt := fun i => by
    rw [formalAdd_eq_law Y p (zc_gp 0) (zc_gp 1), law, sb_gp_self]
    exact Y.intF i
  ph1 := by
    rw [formalAdd_eq_law Y p (zc_gp 0) (zc_gp 1), hAt_eq_sb, hAt_eq_sb, hAt_eq_sb, mvExp_eq (by
      rw [map_sub, map_add (f := _), cc_sb_h Y (zc_gp _) (zc_gp _), cc_sb_h Y (zc_gp _) (zc_gp _),
        cc_sb_h Y (zc_law Y (zc_gp _) (zc_gp _)) (zc_gp _)]
      simp), exp_gauge_cocycle_first_variable Y (zc_gp _) (zc_gp _) (zc_gp _)]
    refine intS_sb V (zc3 (zc_gp _) (zc_gp _) (zc_gp _)) (fun j i => ?_) Y.intPh1
    fin_cases j <;> exact intS_gp V _ i
  ph2 := by
    rw [formalAdd_eq_law Y p (zc_gp 1) (zc_gp 2), hAt_eq_sb, hAt_eq_sb, hAt_eq_sb, mvExp_eq (by
      rw [map_sub, map_add (f := _), cc_sb_h Y (zc_gp _) (zc_gp _), cc_sb_h Y (zc_gp _) (zc_gp _),
        cc_sb_h Y (zc_gp _) (zc_law Y (zc_gp _) (zc_gp _))]
      simp), exp_gauge_cocycle_second_variable Y (zc_gp _) (zc_gp _) (zc_gp _)]
    refine intS_sb V (zc3 (zc_gp _) (zc_gp _) (zc_gp _)) (fun j i => ?_) Y.intPh2
    fin_cases j <;> exact intS_gp V _ i
  sy := by
    have e : (Y.raw p).h = sb ![gp C (Fin dd) (0 : Fin 2), gp C (Fin dd) 1] Y.h := (sb_gp_self Y.h).symm
    rw [hAt_eq_sb, e, mvExp_eq (by
      rw [map_sub, cc_sb_h Y (zc_gp _) (zc_gp _), cc_sb_h Y (zc_gp _) (zc_gp _), sub_zero]),
      exp_sy Y (zc_gp _) (zc_gp _), sb_gp_self]
    exact Y.intSy
  kunit := Y.k_unit
  uint := p.u_int
  sat := fun g => by
    obtain ⟨w, hw, h⟩ := p.u_sat g
    exact ⟨w, hw, fun c c' => ⟨fun e => (h c c').trans (ite_eq_left e),
      fun e => (h c c').trans (ite_eq_right e)⟩⟩ }

theorem rLaw_pairData : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I),
    RLaw (Y.raw p) V :=
  fun _ _ _ _ _ _ _ _ Y _ _ _ _ p => rLaw_raw Y p

end GlobalTheory.RowLawPair
end
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.gaugeAdjointEndPair_elementaryBlock : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) (I0 : Type) [Fintype I0] (p : SelfData Y d I0) (d' : ℕ) (I : Fin 2 → Type) (X : RawChart C d' I (Fin dd)), (X.lg = fun i => un1 (Y.lg i)) → (X.ex = fun i => un1 (Y.ex i)) → X.h = Y.h → ∀ (r s : Fin 2) (M M' : Matrix (Fin dd) (Fin dd) C), IsEnd X V M M' → IsEnd (Y.rawSelf p) V (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = r ∧ y.1 = s then M x.2 y.2 else 0) (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = s ∧ y.1 = r then M' x.2 y.2 else 0) := by
  first | exact @GlobalTheory.RowLaw.EndBlock.isEnd_block | exact GlobalTheory.RowLaw.EndBlock.isEnd_block | (intros; apply GlobalTheory.RowLaw.EndBlock.isEnd_block <;> assumption)
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.hasGaugeAdjointTeichmullerEnd_selfConjugatePlace : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), ∀ g, HasTeich (Y.rawSelf p) V g := by
  first | exact @GlobalTheory.hasTeich_selfData | exact GlobalTheory.hasTeich_selfData | (intros; apply GlobalTheory.hasTeich_selfData <;> assumption)
end

section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv in
theorem siegPairPB_nonempty : ReciprocityTheory.ChartRestriction.G.Pdiv.StSiegPull := by
  intro S S' h M₁ B _ ζ s o f
  have hab : IsAbelianScheme ((Over.pullback f).obj o.A) :=
    { comm := by have := o.ab.comm; infer_instance
      smooth := by have := o.ab.smooth; show Smooth (Limits.pullback.snd _ _); infer_instance
      proper := by have := o.ab.proper; show IsProper (Limits.pullback.snd _ _); infer_instance
      geomConnected := by
        have := o.ab.geomConnected
        show GeometricallyConnected (Limits.pullback.snd _ _); infer_instance }
  have hP := LB.isLB_pull o.isLB (PullbackComparison.pφ₂ f o.A)
  obtain ⟨t₁, ht₁⟩ := o.rig₁
  obtain ⟨t₂, ht₂⟩ := o.rig₂
  exact ⟨{
    A := (Over.pullback f).obj o.A
    ab := hab
    φ := PullbackComparison.pφ f o.A
    φ₂ := PullbackComparison.pφ₂ f o.A
    pb := PullbackComparison.isGrpPullback f o.A
    sq := PullbackComparison.isSquare f o.A
    P := o.P.pull (PullbackComparison.pφ₂ f o.A)
    isLB := hP
    iso := PullbackComparison.gen_refl _ hP
    rig₁ := gen_chartPull (chartPullLinComb o.P _ _ _ _ (PullbackComparison.pφ f o.A)
      (fun _ => PullbackComparison.lift_one_id f o.A)) t₁ ht₁
    rig₂ := gen_chartPull (chartPullLinComb o.P _ _ _ _ (PullbackComparison.pφ f o.A)
      (fun _ => PullbackComparison.lift_id_one f o.A)) t₂ ht₂
    symm := LBIso.chartPull (chartPullPull o.P _ _ rfl)
      (chartPullLinComb o.P _ _ _ _ (PullbackComparison.pφ₂ f o.A) (fun _ => PullbackComparison.lift_swap f o.A)) o.symm }⟩

end GlobalTheory
end
