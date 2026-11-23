module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle511
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle218
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1785
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedQuadraticDatumAtInertPlace
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1786
import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011

@[expose] public section

section

set_option autoImplicit false

namespace GlobalTheory.FactorDepthProd

section General

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {κ : Type} [Fintype κ] {d : κ → ℕ}
  (G : ∀ b, LogFGL v (d b)) {ι : κ → Type} [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C)


omit [Fintype κ] in
theorem constantCoeff_expAlong (x : Σ b, Fin (d b)) : constantCoeff (expAlong G u x) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (by simp)) (by simp) ((isExp_expOf _).1 _)

theorem derivAt0_one_subst (f : MvPowerSeries (Σ b, Fin (d b)) C) :
    derivAt0 1 (subst (expAlong G u) f) = constantCoeff f := by
  classical
  have hs : HasSubst (expAlong G u) := hasSubst_of_constantCoeff_zero (constantCoeff_expAlong G u)
  have h0 : constantCoeff (subst (expAlong G u) (f - (constantCoeff f) • 1)) = 0 :=
    constantCoeff_subst_eq_zero hs (constantCoeff_expAlong G u) (by simp)
  rw [← coe_substAlgHom hs, map_sub, map_smul, map_one, coe_substAlgHom hs] at h0
  unfold derivAt0
  rw [MvPolynomial.support_one, Finset.sum_singleton]
  simpa [mfact, sub_eq_zero] using h0

theorem depth_one : depth G u 1 = 0 := by
  classical
  unfold depth
  refine le_antisymm (iInf_le_of_le ⟨1, fun α => ?_⟩ ?_) (le_iInf fun f => ?_)
  · unfold IsIntV; rw [coeff_one]; split_ifs <;> simp
  · rw [derivAt0_one_subst, map_one, AddValuation.map_one]; rfl
  · rw [derivAt0_one_subst]
    have h : (0 : WithTop ℝ) ≤ v (constantCoeff f.1) := f.2 0
    exact WithBot.coe_le_coe.2 h

theorem depth_prod [CharZero C] [DecidableEq κ] [∀ b, DecidableEq (ι b)] {F : Type} (col : κ → F)
    (P : F → MvPolynomial (Σ b, ι b) C) (hP : ∀ f, ∀ x ∈ (P f).vars, col x.1 = f) (s : Finset F) :
    depth G u (∏ f ∈ s, P f) = ∑ f ∈ s, depth G u (P f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using depth_one G u
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ← ih]
    refine GlobalTheory.T.formalGroupOperatorDepth_mul_disjoint_columns C v κ d G ι u {b | col b = a} _ _ (hP a) fun x hx h => ?_
    obtain ⟨f, hf, hxf⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_prod _ hx)
    exact ha ((show col x.1 = a from h) ▸ hP f x hxf ▸ hf)

theorem depth_prod_detPow [CharZero C] {n : ℕ} (G₀ : LogFGL v n) {F : Type} [Fintype F] (r : F → ℕ)
    (w : ∀ f, Fin (r f) → Fin n → C) (cx : F → ℕ) :
    depth (fun _ : (Σ f : F, Fin (r f)) => G₀) (fun b => w b.1)
      (∏ f : F, MvPolynomial.rename (fun ℓ : (Σ _ : Fin (r f), Fin (r f)) =>
        (⟨⟨f, ℓ.1⟩, ℓ.2⟩ : Σ b : (Σ f : F, Fin (r f)), Fin (r b.1))) (detPow C (r f) (cx f))) =
      ∑ f : F, detDepth G₀ (w f) (cx f) := by
  classical
  rw [depth_prod _ _ (fun b : (Σ f : F, Fin (r f)) => b.1)]
  · refine Finset.sum_congr rfl fun f _ => ?_
    have h := GlobalTheory.T.differentialOperatorDepth_restrict_columns C v (Σ f : F, Fin (r f)) (fun _ => n) (fun _ => G₀)
      (fun b => Fin (r b.1)) (fun b => w b.1) (Fin (r f)) ⟨fun b => ⟨f, b⟩, fun _ _ h => eq_of_heq (Sigma.mk.inj h).2⟩
      (detPow C (r f) (cx f))
    unfold detDepth
    refine Eq.trans ?_ (h.trans ?_)
    · congr 1
    · congr 1
  · intro f x hx
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ hx)
    rfl

end General

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth

theorem nuProdC_eq_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ), nuProdC Ch X cx = ∑ f : Lt1 Dw, nuFacC Ch X f (cx f) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y Ch X cx
  exact depth_prod_detPow (fgl Ch X) rk (frame Ch X) cx

end GlobalTheory.FactorDepthProd
end

section

open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel
open scoped Pointwise

namespace GlobalTheory.PrimFrameMove

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem exists_rightInverse {X : Matrix A D k} (hX : IsPrimFrame (SplitFlip.stdLat k D) X) :
    ∃ R : Matrix D A k, (∀ i j, R i j ∈ 𝒪[k]) ∧ X * R = 1 := by
  have hli : LinearIndependent k X.row := by
    rw [linearIndependent_iff_card_eq_finrank_span, ← hX.1, rank_eq_finrank_span_row]; rfl
  let X' : Matrix A D 𝒪[k] := Matrix.of fun i j => ⟨X i j, mem_matLat_stdLat.1 hX.2.1 i j⟩
  let f : (A → 𝒪[k]) →ₗ[𝒪[k]] (D → 𝒪[k]) := X'.vecMulLinear
  have hf : ∀ v j, ((f v j : 𝒪[k]) : k) = (∑ i, (v i : k) • X.row i) j := fun v j => by
    simp [f, X', vecMul, dotProduct, Finset.sum_apply]
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : ∑ i, (v i : k) • X.row i = 0 := by
      funext j; rw [← hf, hv]; rfl
    funext i
    exact Subtype.ext (Fintype.linearIndependent_iff.1 hli _ h1 i)
  have hsat : ∀ (r : 𝒪[k]) (x : D → 𝒪[k]), r ≠ 0 → r • x ∈ LinearMap.range f → x ∈ LinearMap.range f := by
    rintro r x hr ⟨v, hv⟩
    have hr' : (r : k) ≠ 0 := fun h => hr (Subtype.ext h)
    have h1 : (fun j => (x j : k)) = (r : k)⁻¹ • ∑ i, (v i : k) • X.row i := by
      funext j
      rw [Pi.smul_apply, ← hf, hv]
      simp [hr']
    have h2 : (fun j => (x j : k)) ∈ Submodule.span 𝒪[k] (Set.range X.row) := by
      rw [hX.2.2]
      refine ⟨?_, mem_stdLat.2 fun j => (x j).2⟩
      rw [h1]
      exact Submodule.smul_mem (Submodule.span k _) _
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun 𝒪[k]).1 h2
    refine ⟨d, funext fun j => Subtype.ext ?_⟩
    rw [hf]
    exact congrFun hd j
  have : Module.IsTorsionFree 𝒪[k] ((D → 𝒪[k]) ⧸ LinearMap.range f) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r q h => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    by_cases hr : r = 0
    · exact .inl hr
    · refine .inr ((Submodule.Quotient.mk_eq_zero _).2 (hsat r x hr ?_))
      rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range f).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  obtain ⟨l, hl⟩ : ∃ l : (D → 𝒪[k]) →ₗ[𝒪[k]] (A → 𝒪[k]), l ∘ₗ f = LinearMap.id := by
    have hs' : ∃ s : _ →ₗ[𝒪[k]] _, (LinearMap.range f).mkQ ∘ₗ s = LinearMap.id := ⟨s, hs⟩
    have H := ((LinearMap.exact_map_mkQ_range f).split_tfae hinj (Submodule.mkQ_surjective _)).out 1 2
    exact H.1 hs'
  refine ⟨Matrix.of fun j i => (l (Pi.single j 1) i : k), fun j i => (l (Pi.single j 1) i).2, ?_⟩
  ext i i'
  have h1 : l (f (Pi.single i 1)) = Pi.single i 1 := LinearMap.congr_fun hl _
  have h2 : f (Pi.single i 1) = ∑ j, X' i j • Pi.single j 1 := by
    funext j; simp [f, Finset.sum_apply, Pi.single_apply]

  rw [h2, map_sum] at h1
  have h3 := congrArg Subtype.val (congrFun h1 i')
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h3
  push_cast at h3
  rw [Matrix.mul_apply, Matrix.one_apply]
  refine h3.trans ?_
  rw [Pi.single_apply]
  by_cases h : i = i'
  · simp [h]
  · simp [h, Ne.symm h]

theorem exists_mem_glLatCong {u : kˣ} (hu : valuation k (u : k) < 1) {M : Matrix D D k}
    (hM : ∀ i j, valuation k (M i j) ≤ valuation k (u : k)) :
    ∃ κ ∈ glLatCong u (SplitFlip.stdLat k D), κ.val = 1 + M := by
  let M' : Matrix D D 𝒪[k] := Matrix.of fun i j => ⟨M i j, (hM i j).trans hu.le⟩
  have hK : IsUnit (1 + M') := by
    rw [Matrix.isUnit_iff_isUnit_det, ← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have : (IsLocalRing.residue 𝒪[k]).mapMatrix M' = 0 := by
      ext r j
      simp only [RingHom.mapMatrix_apply, map_apply, Matrix.zero_apply]
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Valuation.Integer.not_isUnit_iff_valuation_lt_one]
      exact (hM r j).trans_lt hu
    rw [map_add (f := _), this]; simp
  obtain ⟨w, hw⟩ := hK
  have hv : (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) w).val = 1 + M := by
    show (algebraMap 𝒪[k] k).mapMatrix w.val = _
    rw [hw, map_add (f := _), map_one]; rfl
  refine ⟨_, GlobalTheory.FunObj.GivenAdm.mem_glLatCong.2 ⟨⟨w, rfl⟩, ?_⟩, hv⟩
  rw [hv, add_sub_cancel_left]
  exact hM


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem vecMul_diagGL_mem (a b c : D → kˣ) (h : ∀ j, b j = a j * c j) (x : D → k) :
    x ᵥ* (diagGL c).val ∈ diagLat b ↔ x ∈ diagLat a := by
  refine forall_congr' fun j => ?_
  have h0 : 0 < valuation k (c j : k) := zero_lt_iff.2 (by simp)
  rw [diagGL_val, vecMul_diagonal, map_mul, h, Units.val_mul, map_mul]
  exact mul_le_mul_iff_left₀ h0

theorem exists_glLatCong_move (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (c : D → kˣ) (u : kˣ) (hu : valuation k (u : k) < 1) (X Z : Matrix A D k) (hX : IsPrimFrame (diagLat c) X)
    (hZ : Z ∈ matLat A (u • diagLat c)) : ∃ κ ∈ glLatCong u (diagLat c), X + Z = X * κ.val := by
  set g : GL D k := diagGL c with hg
  have h1 : ∀ x, x ᵥ* g.val ∈ diagLat c ↔ x ∈ SplitFlip.stdLat k D := vecMul_diagGL_mem 1 c c (by simp)
  have h2 : ∀ x, x ᵥ* g.val ∈ u • diagLat c ↔ x ∈ u • SplitFlip.stdLat k D := fun x => by
    rw [SplitFlip.stdLat, smul_diagLat, smul_diagLat]
    exact vecMul_diagGL_mem _ _ c (by simp) x
  have h1' : ∀ x, x ᵥ* (g⁻¹).val ∈ SplitFlip.stdLat k D ↔ x ∈ diagLat c := fun x => by
    rw [← h1, vecMul_vecMul, Units.inv_mul, vecMul_one]
  have h2' : ∀ x, x ᵥ* (g⁻¹).val ∈ u • SplitFlip.stdLat k D ↔ x ∈ u • diagLat c := fun x => by
    rw [← h2, vecMul_vecMul, Units.inv_mul, vecMul_one]
  obtain ⟨R, hR, hXR⟩ := exists_rightInverse (SplitFlip.Model.isPrimFrame_mul hX g⁻¹ h1')
  have hZ' : GlobalTheory.FunObj.GivenAdm.CongM u (Z * (g⁻¹).val) :=
    GlobalTheory.FunObj.GivenAdm.mem_matLat_smul.1 fun i => (h2' (Z.row i)).2 (hZ i)
  obtain ⟨κ, ⟨hκ, hκ'⟩, hv⟩ := exists_mem_glLatCong hu (hZ'.mul_left (Y := R) hR)
  refine ⟨g⁻¹ * κ * g, ⟨fun x => ?_, fun x hx => ?_⟩, ?_⟩
  · rw [Units.val_mul, Units.val_mul, ← vecMul_vecMul, ← vecMul_vecMul, h1, hκ, h1']
  · rw [show (g⁻¹ * κ * g).val - 1 = (g⁻¹).val * (κ.val - 1) * g.val by
      rw [mul_sub, sub_mul, mul_one, Units.inv_mul, Units.val_mul, Units.val_mul],
      ← vecMul_vecMul, ← vecMul_vecMul, h2]
    exact hκ' _ ((h1' x).2 hx)
  · rw [Units.val_mul, Units.val_mul, hv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_add,
      ← Matrix.mul_assoc _ R, hXR, Matrix.mul_one, Matrix.one_mul, ← Matrix.add_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]

end GlobalTheory.PrimFrameMove
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT.ThBasic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cj_mem_integers (hU : Unr E) (w : Pl E) (x : w.adicCompletion E) (hx : x ∈ Ov E w) : cj w x ∈ Ov E w := by
  have h := (GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.1 x
  change Valued.v (cj w x) ≤ 1
  rw [h]; exact hx

theorem thL_thL (hU : Unr E) (n : ℕ) (w : Pl E) (g : GLw n w) : thL n w (thL n w g) = g := by
  unfold thL
  split_ifs
  · rfl
  · exact GlobalTheory.ThetaPull.thetaGL_thetaGL _ (GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.1 g

theorem continuous_thL (hU : Unr E) (n : ℕ) (w : Pl E) : Continuous (thL n w) := by
  unfold thL
  split_ifs
  · exact continuous_id
  · exact GlobalTheory.ThetaPull.continuous_thetaGL _ (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1

theorem thL_mem_KGL (hU : Unr E) (n : ℕ) (w : Pl E) (k : GLw n w) (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) :
    thL n w k ∈ GlobalTheory.LFun.KGL w (n := n) := by
  unfold thL
  split_ifs
  · exact hk
  · obtain ⟨k', rfl⟩ := hk
    let c' : Ov E w →+* Ov E w := (cj w).restrict (Ov E w) (Ov E w) (cj_mem_integers hU w)
    refine ⟨thetaGL n c' k', ?_⟩
    exact GlobalTheory.ThetaPull.map_thetaGL (Ov E w).subtype c' (cj w) (fun x => rfl) k'

theorem nrmL_twist (hU : Unr E) (n : ℕ) (w : Pl E) (g y : GLw n w) :
    nrmL n w (g⁻¹ * y * thL n w g) = g⁻¹ * nrmL n w y * g := by
  unfold nrmL
  have h2 := thL_thL hU n w g
  unfold thL at h2 ⊢
  split_ifs with hs
  · simp [hs] at *
  · simp only [hs, if_false] at h2 ⊢
    rw [map_mul, map_mul, map_inv, h2]
    group

theorem isClosed_UL (hU : Unr E) (n : ℕ) (w : Pl E) : IsClosed (UL n w : Set (GLw n w)) := by
  unfold UL
  split_ifs
  · exact isClosed_univ
  · have hc := (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1
    have : Continuous fun g : GLw n w => cT (cj w) (g : Matrix (Fin n) (Fin n) _) * 1 * (g : Matrix (Fin n) (Fin n) _) := by
      refine Continuous.mul (Continuous.mul ?_ continuous_const) Units.continuous_val
      exact continuous_matrix fun i j => hc.comp (Units.continuous_val.matrix_elem _ _)
    exact isClosed_singleton.preimage this

theorem charpoly_nrmL (hU : Unr E) (n : ℕ) (w : Pl E) (δ : GL (Fin n) E) :
    (nrmL n w (locEl n w δ)).val.charpoly = atPl w (δ * thE E n δ).val.charpoly := by
  unfold nrmL locEl
  split_ifs with hs
  · exact (Matrix.charpoly_map _ _)
  · have hm : thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ) =
        GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (thE E n δ) :=
      (GlobalTheory.ThetaPull.map_thetaGL _ _ _ (fun x => ((GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.2.1 hs).1 x |>.symm) δ).symm
    rw [hm, ← map_mul]
    exact (Matrix.charpoly_map _ _)

theorem cLoc_mem_UL (hU : Unr E) (n : ℕ) (w : Pl E) (x : UA E n) : cLoc w x ∈ UL n w := by
  unfold UL
  split_ifs with hs
  · exact Subgroup.mem_top _
  · have hp := ((GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.2.1 hs).2.2.1
    have hx := x.2
    change cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * (x.1 : Matrix (Fin n) (Fin n) (Ad E)) = 1 at hx
    change cT (cj w) ((cLoc w x : GLw n w) : Matrix (Fin n) (Fin n) _) * 1 * ((cLoc w x : GLw n w) : Matrix (Fin n) (Fin n) _) = 1
    have := congrArg (((pLoc E w).comp (pFin E)).mapMatrix) hx
    rw [map_one, map_mul, map_mul, map_one] at this
    convert this using 3
    · refine Matrix.ext fun i j => ?_
      show cj w (pLoc E w (pFin E ((x.1 : Matrix (Fin n) (Fin n) (Ad E)) j i))) =
        pLoc E w (pFin E (conjAd E ((x.1 : Matrix (Fin n) (Fin n) (Ad E)) j i)))
      rw [← hp]
      rfl
    · rfl

theorem twist_basic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), Continuous (thL n w) ∧ (∀ g, thL n w (thL n w g) = g) ∧ (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), thL n w k ∈ GlobalTheory.LFun.KGL w (n := n)) ∧ (∀ g y, nrmL n w (g⁻¹ * y * thL n w g) = g⁻¹ * nrmL n w y * g) ∧ IsOpen (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ∧ IsCompact (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ∧ IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧ (∀ δ : GL (Fin n) E, (nrmL n w (locEl n w δ)).val.charpoly = atPl w (δ * thE E n δ).val.charpoly) ∧ ∀ x ∈ locU n w, cLoc w x ∈ UL n w := by
  intro E _ _ _ hU n w
  have hK := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  refine ⟨continuous_thL hU n w, thL_thL hU n w, thL_mem_KGL hU n w, nrmL_twist hU n w, hK.1, hK.2, ?_, ?_,
    charpoly_nrmL hU n w, fun x _ => cLoc_mem_UL hU n w x⟩
  · rw [KL, Subgroup.coe_subgroupOf]
    exact hK.1.preimage continuous_subtype_val
  · rw [KL, Subgroup.coe_subgroupOf]
    exact (isClosed_UL hU n w).isClosedEmbedding_subtypeVal.isCompact_preimage hK.2

end GlobalTheory.BCT.ThBasic
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.inert_integral_twistedConjugates_twistedCentralizer_mul_maxCompact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), ¬ IsSplitAt w →
    ∀ y g : GLw n w, y ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w y).val.charpoly + v * derivative (nrmL n w y).val.charpoly = 1) →
    g⁻¹ * y * thL n w g ∈ GlobalTheory.LFun.KGL w (n := n) → ∃ t ∈ twCent (thL n w) y, ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), g = t * k := by
  first | exact @GlobalTheory.InertUniq.eq_twCent_mul_KGL | exact GlobalTheory.InertUniq.eq_twCent_mul_KGL | (intros; apply GlobalTheory.InertUniq.eq_twCent_mul_KGL <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.toricSum_coordinate_isAlgebraic : ∀ (hA : LatAlg) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (Λ₀ : PeriodPair) (Ω₀ : ℂ) (hΛ : IsLatOf ι 1 Λ₀) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (T : ℂ) (hV : IsValSum φ s κ 𝔣 Q χ T), IsAlgebraic ℚ (coordIn E d s κ Ω₀ T) := by
  first | exact @GlobalTheory.ToricCoordAlg.isAlgebraic_coordIn | exact GlobalTheory.ToricCoordAlg.isAlgebraic_coordIn | (intros; apply GlobalTheory.ToricCoordAlg.isAlgebraic_coordIn <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

theorem _root_.GlobalTheory.T.full_algebra_part_le_split_hecke_part : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → ∀ SF, IsSF R SF → ∀ (c : Pl D.host.E → List ℤ → ℂ) (Sg : Pl0 → ℂ[X]), ((∀ P ∈ A.ok A.μ0, Sg P = Formalism.L2.Col.heckePolyOf D.R.r (A.q P) fun k => c (R.pl P) (dualLab (splitLab D.R.r k))) → ∀ x ∈ EEc R SF c, R.HE.e x ∈ hPart (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (A.ok A.μ0) R.pl A.q Sg) ∧ ∀ i, (∀ P ∈ A.ok A.μ0, Sg P = Formalism.L2.Col.heckePolyOf D.R.r (A.q P) fun k => c (R.pl P) (splitLab D.R.r k)) → ∀ x ∈ Wcc R SF i c, (R.HW i _).e x ∈ hPart (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok A.μ0) R.pl A.q Sg := by
  first | exact @GlobalTheory.HeckeSplitPart.parts_in_hPart | exact GlobalTheory.HeckeSplitPart.parts_in_hPart | (intros; apply GlobalTheory.HeckeSplitPart.parts_in_hPart <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.LabEq

theorem dualLab_dualLab' (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse]

theorem dualLab_length' (d : List ℤ) : (dualLab d).length = d.length := by
  simp [dualLab]

theorem dualLab_pairwise' (d : List ℤ) :
    (dualLab d).Pairwise (fun a b => b ≤ a) ↔ d.Pairwise (fun a b => b ≤ a) := by
  simp [dualLab, List.pairwise_reverse, List.pairwise_map]

theorem isLab_W_iff : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, Core R F → ∀ i P d, Good R A.μ0 P → (IsLab (Wc D i) P d ↔ IsLab (Yc D 0) P (dualLab d)) ∧ (IsLab (Wc D i) P d ↔ IsLab (Yc D 0) P d) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s _ i P d _
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hY : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _)]
    simp [Ranks.rankY]
  rw [GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing, GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing, GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing, hW, hY, dualLab_length', dualLab_pairwise', dualLab_dualLab']
  refine ⟨?_, Iff.rfl⟩
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun h => (h3 h).symm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun h => (h3 h).symm⟩

end GlobalTheory.LabEq
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.exists_unramifiedQuadraticDatum_at_inertPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, ¬ IsSplitAt w → ∃ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) ∧ (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) ∧ (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) ∧ qV E w = K.q ^ 2 := by
  first | exact @GlobalTheory.InertUQ.exists_uq | exact GlobalTheory.InertUQ.exists_uq | (intros; apply GlobalTheory.InertUQ.exists_uq <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.unitLemma_unramified_product_unitary_groups : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.unitLemma_identity_unconditional | exact GlobalTheory.UnitLemma.unitLemma_identity_unconditional | (intros; apply GlobalTheory.UnitLemma.unitLemma_identity_unconditional <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.bundleIso_local_units_comp_of_pullback_sections : ∀ (X Y' Y : Scheme.{0}) (b' : Y' ⟶ X) (β : Y ⟶ Y') (b : Y ⟶ X), β ≫ b' = b → ∀ (A : LB X) (H' : LB Y') (H : LB Y) (w' : LB.Iso H' (A.pull b')) (v : LB.Iso H (H'.pull β)) (w : LB.Iso H (A.pull b)) (ι : Type) (s : ι → LB.Sec A) (s' : ι → LB.Sec H') (s'' : ι → LB.Sec H), (∀ j, Rel b' w' (s j) (s' j)) → (∀ j, Rel β v (s' j) (s'' j)) → (∀ j, Rel b w (s j) (s'' j)) → (⨆ j, nonzeroLocus (s'' j) = ⊤) → ∀ z k k' k'', b z ∈ A.U k → β z ∈ H'.U k' → z ∈ H.U k'' → Geo.Tor.gw w (𝟙 _) z k k'' = Geo.Tor.gw w' β z k k' * Geo.Tor.gw v (𝟙 _) z k' k'' := by
  first | exact @GlobalTheory.FormalAlg.gw_comp_of_rel | exact GlobalTheory.FormalAlg.gw_comp_of_rel | (intros; apply GlobalTheory.FormalAlg.gw_comp_of_rel <;> assumption)
end
