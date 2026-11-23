module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle020
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.ContinuousLev
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.RapidDecay
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.GlobalFields.Adele.Topology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Cm
open GlobalTheory.ConstTermSmooth (Good constTerm_mem_Sm)

attribute [local instance 10000] MeasurableSpace.pi

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

private theorem ct_sm (r : ℕ) {φ : Sm E n} (h : Good φ) : constantTerm r φ.1 ∈ Sm E n ∧
    ∀ X g, lieD X (constantTerm r φ.1) g = constantTerm r (lie E n X φ).1 g := by
  have hL : ratN E n r = unipLattice E n r := AddSubgroup.ext fun x =>
    ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩
  have hu : ∀ x : UPos n r → AdeleRing (𝓞 E) E, unip x = unipGL x := fun x => Units.ext rfl
  have hF : IsAddFundamentalDomain (ratN E n r) (unipFundamentalDomain E n r) (unipMeasure E n r) := by
    rw [hL]; exact isAddFundamentalDomain_unipFundamentalDomain
  have key := constTerm_mem_Sm E n r (unipMeasure E n r) (unipFundamentalDomain E n r) inferInstance hF
    (unipMeasure_unipFundamentalDomain r) φ h.1 h.2
  simp only [hu] at key
  exact key

private theorem good_add {φ ψ : Sm E n} (h₁ : Good φ) (h₂ : Good ψ) : Good (φ + ψ) := by
  refine ⟨fun γ g => ?_, isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
    ((h₁.2.inter h₂.2).mem_nhds ⟨by simp, by simp⟩) fun k hk => ?_)⟩
  · change φ.1 _ + ψ.1 _ = φ.1 _ + ψ.1 _
    rw [h₁.1 γ g, h₂.1 γ g]
  · change GlobalTheory.CuspRep.finRep E n k _ = _
    rw [map_add (f := _), hk.1, hk.2]

private theorem good_smul {φ : Sm E n} (h : Good φ) (c : ℂ) : Good (c • φ) := by
  refine ⟨fun γ g => ?_, isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
    (h.2.mem_nhds (by simp)) fun k hk => ?_)⟩
  · change c * φ.1 _ = c * φ.1 _
    rw [h.1 γ g]
  · change GlobalTheory.CuspRep.finRep E n k _ = _
    rw [map_smul, show GlobalTheory.CuspRep.finRep E n k φ = φ from hk]

private def pas (r : ℕ) : Subalgebra ℂ (Module.End ℂ (Sm E n)) where
  carrier := {T | ∀ φ : Sm E n, Good φ → Good (T φ) ∧
    ∀ F : Sm E n, F.1 = constantTerm r φ.1 → (T F).1 = constantTerm r (T φ).1}
  mul_mem' := fun ha hb φ h => ⟨(ha _ (hb φ h).1).1, fun F hF => (ha _ (hb φ h).1).2 _ ((hb φ h).2 F hF)⟩
  add_mem' := fun {a b} ha hb φ h => ⟨good_add (ha φ h).1 (hb φ h).1, fun F hF => funext fun g => by
    change (a F).1 g + (b F).1 g = constantTerm r ((a φ).1 + (b φ).1) g
    rw [(ha φ h).2 F hF, (hb φ h).2 F hF, constantTerm_add (ContAut.continuous_of_isOpen_stab E n _ (ha φ h).1.2)
      (ContAut.continuous_of_isOpen_stab E n _ (hb φ h).1.2)]⟩
  algebraMap_mem' c φ h := ⟨good_smul h c, fun F hF => funext fun g => by
    change c • F.1 g = constantTerm r (c • φ.1) g
    rw [hF, constantTerm_smul]⟩

private theorem of_lie (S : Subalgebra ℂ (Module.End ℂ (Sm E n))) (h : ∀ X, lie E n X ∈ S) (u : UC E n) :
    uC E n u ∈ S := by
  have hι : ∀ X, ιC E n X ∈ S.comap (uC E n) := fun X => by
    rw [Subalgebra.mem_comap, uC_ιC]; exact h X
  have h : Algebra.adjoin ℂ {x : UC E n | ∃ τ i j, x = genC τ i j} ≤ S.comap (uC E n) :=
    Algebra.adjoin_le (by
      rintro _ ⟨τ, i, j, rfl⟩
      rw [genC, UpperTheory.V.AlgRepEndIrreducible.eL]
      exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (hι _) (Subalgebra.smul_mem _ (hι _) _)) _)
  exact h (adjoin_genC (E := E) (a := n) ▸ Algebra.mem_top)

private theorem lie_pas (r : ℕ) (X : Lie E n) : lie E n X ∈ (pas r : Subalgebra ℂ (Module.End ℂ (Sm E n))) :=
  fun φ h => ⟨h.lie X, fun F hF => funext fun g => by
    rw [lie_apply, hF]
    exact (ct_sm r h).2 X g⟩

omit [_root_.NumberField.IsTotallyComplex E] in
private theorem ct_unip {r : ℕ} {φ : AdelicGLn.AdelicGL E n → ℂ} (hφ : IsLeftInvariant φ)
    (Y : UPos n r → AdeleRing (𝓞 E) E) (g : AdelicGLn.AdelicGL E n) :
    constantTerm r φ (unipGL Y * g) = constantTerm r φ g := by
  have hD : IsAddFundamentalDomain (unipLattice E n r) ((fun X => X + -Y) ⁻¹' unipFundamentalDomain E n r)
      (unipMeasure E n r) :=
    isAddFundamentalDomain_unipFundamentalDomain.preimage_of_equiv
      (measurePreserving_add_right _ (-Y)).quasiMeasurePreserving Function.bijective_id fun ξ X => by
        change ((ξ : UPos n r → AdeleRing (𝓞 E) E) + X) + -Y = ξ + (X + -Y)
        rw [add_assoc]
  rw [constantTerm_eq_setIntegral hφ hD g, constantTerm,
    ← (measurePreserving_add_right (unipMeasure E n r) (-Y)).setIntegral_preimage_emb (measurableEmbedding_addRight _)]
  simp only [← mul_assoc, ← unipGL_add, neg_add_cancel_right]

end UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.ConvolutionTheory.BW.ctOps :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.CtOps E := by
  intro E _ _ _ r s φ h
  have hg : Good φ := ⟨h.left, h.level⟩
  refine ⟨⟨_, (UpperTheory.ConvolutionTheory.BW.ct_sm r hg).1⟩, rfl, fun x g => ?_, fun γ g => ?_, fun u =>
    (UpperTheory.ConvolutionTheory.BW.of_lie _ (UpperTheory.ConvolutionTheory.BW.lie_pas r) u φ hg).2 _ rfl⟩
  · rw [show unip x = unipGL x from Units.ext rfl]
    exact UpperTheory.ConvolutionTheory.BW.ct_unip h.left x g
  · have := UpperTheory.ConvolutionTheory.BW.Pair.ct_lev_rat (φ := rightTranslate g φ.1) (fun γ x => by
      simp only [rightTranslate, mul_assoc]; exact h.left γ _) γ.1 γ.2 1 1
    rw [constantTerm_rightTranslate, constantTerm_rightTranslate, mul_one, mul_one, Prod.mk_one_one, map_one, one_mul] at this
    exact this
end
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep GroundTheory.Automorphic UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

private theorem lie_right_translate_comm (X : Lie E n) (y : GL (Fin n) (Cinf E)) (k : GL (Fin n) (Af E)) :
    ∃ X' : Lie E n, lie E n X * rt E n (infGL E n y * finGL E n k) =
      rt E n (infGL E n y * finGL E n k) * lie E n X' := by
  refine ⟨toL ((y⁻¹).val * Matrix.of X * y.val), ?_⟩
  have h := GlobalTheory.CapAdInv.rt_lie y ((y⁻¹).val * Matrix.of X * y.val)
  have e : y.val * ((y⁻¹).val * Matrix.of X * y.val) * (y⁻¹).val = Matrix.of X := by
    simp [mul_assoc]
  rw [e] at h
  have h' : lie E n (toL (Matrix.of X)) = lie E n X := rfl
  rw [h'] at h
  rw [map_mul, ← mul_assoc, ← h, mul_assoc, mul_assoc, lie_rt_fin, mul_assoc]

private theorem lie_comm (X : Lie E n) (g : GA E n) :
    ∃ X' : Lie E n, lie E n X * rt E n g = rt E n g * lie E n X' := by
  have h := lie_right_translate_comm X (Matrix.GeneralLinearGroup.map (pInf E) g) (Matrix.GeneralLinearGroup.map (pFin E) g)
  rwa [infGL_mul_finGL] at h

private def itw (g : GA E n) : Subalgebra ℂ (UC E n) where
  carrier := {u | ∃ u', uC E n u * rt E n g = rt E n g * uC E n u'}
  mul_mem' := by
    rintro a b ⟨a', ha⟩ ⟨b', hb⟩
    exact ⟨a' * b', by rw [map_mul, mul_assoc, hb, ← mul_assoc, ha, map_mul, mul_assoc]⟩
  add_mem' := by
    rintro a b ⟨a', ha⟩ ⟨b', hb⟩
    exact ⟨a' + b', by rw [map_add (f := _), add_mul, ha, hb, map_add (f := _), mul_add]⟩
  algebraMap_mem' r := ⟨algebraMap _ _ r, by rw [AlgHom.commutes]; exact Algebra.commutes _ _⟩

private theorem ιC_mem (g : GA E n) (X : Lie E n) : ιC E n X ∈ itw g := by
  obtain ⟨X', h⟩ := lie_comm X g
  exact ⟨ιC E n X', by rw [uC_ιC, uC_ιC]; exact h⟩

private theorem genC_mem (g : GA E n) (τ : E →+* ℂ) (i j : Fin n) : genC τ i j ∈ itw g := by
  rw [genC, UpperTheory.V.AlgRepEndIrreducible.eL]
  exact (itw g).smul_mem ((itw g).sub_mem (ιC_mem g _) ((itw g).smul_mem (ιC_mem g _) _)) _

private theorem exists_comm (g : GA E n) (u : UC E n) :
    ∃ u', uC E n u * rt E n g = rt E n g * uC E n u' := by
  have h : Algebra.adjoin ℂ {x : UC E n | ∃ τ i j, x = genC τ i j} ≤ itw g :=
    Algebra.adjoin_le (by rintro _ ⟨τ, i, j, rfl⟩; exact genC_mem g τ i j)
  exact h (adjoin_genC (E := E) (a := n) ▸ Algebra.mem_top)

private theorem zop_comm_rt (P : MvPolynomial ((E →+* ℂ) × Fin n) ℂ) (g : GA E n) :
    Commute (zop P) (rt E n g) := by
  refine GlobalTheory.CompanionTheory.CTFin.Slice1.commute_rt_of_mem_Zalg ?_ g
  rw [Zalg_eq_map]
  exact ⟨_, (evZ E n P).2, rfl⟩

private theorem zop_comm_uC (P : MvPolynomial ((E →+* ℂ) × Fin n) ℂ) (v : UC E n) :
    zop P * uC E n v = uC E n v * zop P := by
  have h := Subalgebra.mem_center_iff.1 (evZ E n P).2 v
  unfold zop
  rw [← map_mul, ← map_mul, h]

private theorem bnd_mono {C : ℝ} (hC : 0 ≤ C) (B : ℝ) (d : ℕ) (g : GA E n) {N M : ℕ} (h : N ≤ M) :
    B * C ^ d * AutomorphicForm.height g ^ N ≤ |B| * C ^ d * AutomorphicForm.height g ^ M := by
  have h1 := AutomorphicForm.one_le_height g
  have h2 : AutomorphicForm.height g ^ N ≤ AutomorphicForm.height g ^ M := pow_le_pow_right₀ h1 h
  have h3 : 0 ≤ C ^ d := pow_nonneg hC d
  have h4 : 0 ≤ AutomorphicForm.height g ^ N := pow_nonneg (zero_le_one.trans h1) N
  exact mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self B) h3) h2 h4 (mul_nonneg (abs_nonneg B) h3)

private theorem band_zero (C : ℝ) : Band C (0 : Sm E n) :=
  { toUmg := ((umgOps E) n).1
    band := ⟨0, fun u => ⟨0, fun α g => by simp⟩⟩ }

private theorem band_add {C : ℝ} (hC : 0 ≤ C) {φ ψ : Sm E n} (h₁ : Band C φ) (h₂ : Band C ψ) : Band C (φ + ψ) := by
  refine { toUmg := (((umgOps E) n).2 φ h₁.toUmg).2.1 ψ h₂.toUmg, band := ?_ }
  obtain ⟨N, hN⟩ := h₁.band
  obtain ⟨M, hM⟩ := h₂.band
  refine ⟨max N M, fun u => ?_⟩
  obtain ⟨B, hB⟩ := hN u
  obtain ⟨D, hD⟩ := hM u
  refine ⟨|B| + |D|, fun α g => ?_⟩
  rw [map_add (f := _), map_add (f := _)]
  refine (norm_add_le _ _).trans ?_
  have := (hB α g).trans (bnd_mono hC B α.degree g (le_max_left N M))
  have := (hD α g).trans (bnd_mono hC D α.degree g (le_max_right N M))
  rw [add_mul, add_mul]
  exact add_le_add ‹_› ‹_›

private theorem band_smul {C : ℝ} {φ : Sm E n} (h : Band C φ) (c : ℂ) : Band C (c • φ) := by
  refine { toUmg := (((umgOps E) n).2 φ h.toUmg).2.2.1 c, band := ?_ }
  obtain ⟨N, hN⟩ := h.band
  refine ⟨N, fun u => ?_⟩
  obtain ⟨B, hB⟩ := hN u
  refine ⟨‖c‖ * B, fun α g => ?_⟩
  rw [map_smul, map_smul]
  show ‖c • (uC E n u (zop (MvPolynomial.monomial α 1) φ)).1 g‖ ≤ _
  rw [norm_smul, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg c)
  rw [← mul_assoc]
  exact hB α g

private theorem band_uC {C : ℝ} {φ : Sm E n} (h : Band C φ) (v : UC E n) : Band C (uC E n v φ) := by
  refine { toUmg := (((umgOps E) n).2 φ h.toUmg).2.2.2.1 v, band := ?_ }
  obtain ⟨N, hN⟩ := h.band
  refine ⟨N, fun u => ?_⟩
  obtain ⟨B, hB⟩ := hN (u * v)
  refine ⟨B, fun α g => ?_⟩
  have e : uC E n u (zop (MvPolynomial.monomial α 1) (uC E n v φ)) =
      uC E n (u * v) (zop (MvPolynomial.monomial α 1) φ) := by
    rw [← Module.End.mul_apply (zop _), zop_comm_uC, map_mul]
    rfl
  rw [e]
  exact hB α g

private theorem band_rt {C : ℝ} (hC : 0 ≤ C) {φ : Sm E n} (h : Band C φ) (g : GA E n) : Band C (rt E n g φ) := by
  refine { toUmg := (((umgOps E) n).2 φ h.toUmg).2.2.2.2.1 g, band := ?_ }
  obtain ⟨N, hN⟩ := h.band
  refine ⟨N, fun u => ?_⟩
  obtain ⟨u', hu⟩ := exists_comm g u
  obtain ⟨B, hB⟩ := hN u'
  have hc : 0 ≤ AutomorphicForm.heightConst E n * AutomorphicForm.height g :=
    mul_nonneg (zero_le_one.trans AutomorphicForm.one_le_heightConst) (AutomorphicForm.height_pos g).le
  refine ⟨|B| * (AutomorphicForm.heightConst E n * AutomorphicForm.height g) ^ N, fun α x => ?_⟩
  have e : uC E n u (zop (MvPolynomial.monomial α 1) (rt E n g φ)) =
      rt E n g (uC E n u' (zop (MvPolynomial.monomial α 1) φ)) := by
    rw [← Module.End.mul_apply (zop _), (zop_comm_rt _ g).eq, Module.End.mul_apply,
      ← Module.End.mul_apply (uC E n u), hu]
    rfl
  rw [e]
  show ‖(uC E n u' (zop (MvPolynomial.monomial α 1) φ)).1 (x * g)‖ ≤ _
  refine (hB α (x * g)).trans ((bnd_mono hC B α.degree (x * g) le_rfl).trans ?_)
  have h3 : 0 ≤ |B| * C ^ α.degree := mul_nonneg (abs_nonneg B) (pow_nonneg hC _)
  have h4 : AutomorphicForm.height (x * g) ≤
      AutomorphicForm.heightConst E n * AutomorphicForm.height g * AutomorphicForm.height x := by
    have := AutomorphicForm.height_mul_le x g
    nlinarith [this]
  calc |B| * C ^ α.degree * AutomorphicForm.height (x * g) ^ N
      ≤ |B| * C ^ α.degree * (AutomorphicForm.heightConst E n * AutomorphicForm.height g * AutomorphicForm.height x) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (AutomorphicForm.height_pos _).le h4 N) h3
    _ = _ := by rw [mul_pow]; ring

private theorem band_finsum {C : ℝ} (hC : 0 ≤ C) {Q : Type*} (f : Q → Module.End ℂ (Sm E n)) {φ : Sm E n}
    (hf : ∀ c, Band C (f c φ)) : Band C ((∑ᶠ c, f c) φ) := by
  classical
  by_cases h : (Function.support f).Finite
  · rw [finsum_eq_sum_of_support_subset (s := h.toFinset) _ (by simp), LinearMap.sum_apply]
    exact Finset.sum_induction _ (Band C) (fun _ _ => band_add hC) (band_zero C) fun c _ => hf c
  · rw [finsum_of_infinite_support h]
    exact band_zero C

private theorem band_hk {C : ℝ} (hC : 0 ≤ C) {φ : Sm E n} (h : Band C φ) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) (j : ℕ) :
    Band C (hk n w j φ) := by
  unfold hk
  rw [LinearMap.smul_apply]
  refine band_smul (band_finsum hC _ fun c => ?_) _
  rw [LinearMap.smul_apply]
  exact band_smul (band_rt hC h _) _

end UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.ConvolutionTheory.BW.bandOps :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.BandOps E := by
  intro E _ _ _ n C hC
  exact ⟨UpperTheory.ConvolutionTheory.BW.band_zero C, fun φ h => ⟨fun ψ h₂ => UpperTheory.ConvolutionTheory.BW.band_add hC h h₂, UpperTheory.ConvolutionTheory.BW.band_smul h,
    UpperTheory.ConvolutionTheory.BW.band_uC h, UpperTheory.ConvolutionTheory.BW.band_rt hC h, fun w j => UpperTheory.ConvolutionTheory.BW.band_hk hC h w j⟩⟩
end
end

section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] {r s : ℕ}

private theorem ht_zt (t : ℝ) : AutomorphicForm.height (zt E r t) ≤
    Real.exp |t| ^ (2 * Fintype.card (InfinitePlace E)) := by
  set e : ℝ := ((r * Module.finrank ℚ E : ℝ))⁻¹ with he
  have hL : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg t)
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 := by
    rw [he, ← Nat.cast_mul]
    exact Nat.cast_inv_le_one _
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ Real.exp |t| → x ^ e ≤ Real.exp |t| := fun x hx hxL =>
    calc x ^ e ≤ Real.exp |t| ^ e := Real.rpow_le_rpow hx hxL he0
      _ ≤ Real.exp |t| ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL he1
      _ = Real.exp |t| := Real.rpow_one _
  refine CuspidalSpectrum.height_diagUnits_posIdele_le (K := E) (n := r) (ρ := fun _ => Real.exp t ^ e)
    (fun _ => Real.rpow_pos_of_pos (Real.exp_pos t) e) hL
    fun _ => ⟨key _ (Real.exp_pos t).le (Real.exp_le_exp.2 (le_abs_self t)), ?_⟩
  rw [← Real.inv_rpow (Real.exp_pos t).le, ← Real.exp_neg]
  exact key _ (Real.exp_pos _).le (Real.exp_le_exp.2 (neg_le_abs t))

private theorem ct_bd (n r N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : AdelicGLn.AdelicGL E n → ℂ) (B : ℝ), 0 ≤ B →
    (∀ g, ‖φ g‖ ≤ B * AutomorphicForm.height g ^ N) →
    ∀ g, ‖constantTerm r φ g‖ ≤ C * B * AutomorphicForm.height g ^ N := by
  obtain ⟨D, hD, hsub⟩ := exists_isCompact_superset_unipFundamentalDomain (K := E) (n := n) (r := r)
  obtain ⟨M, hM⟩ := CuspidalSpectrum.exists_height_le_of_isCompact (hD.image continuous_unipGL)
  have hc0 : 0 ≤ heightConst E n := le_trans zero_le_one one_le_heightConst
  have hfin : unipMeasure E n r (unipFundamentalDomain E n r) < ⊤ :=
    (measure_mono hsub).trans_lt hD.measure_lt_top
  refine ⟨(heightConst E n * |M|) ^ N * (unipMeasure E n r).real (unipFundamentalDomain E n r), by positivity,
    fun φ B hB hφ g => ?_⟩
  have hg := (height_pos g).le
  have hb : ∀ X ∈ unipFundamentalDomain E n r,
      ‖φ (unipGL X * g)‖ ≤ B * (heightConst E n * |M| * AutomorphicForm.height g) ^ N := by
    intro X hX
    have h1 : AutomorphicForm.height (unipGL X * g) ≤ heightConst E n * |M| * AutomorphicForm.height g :=
      (height_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ((hM _ ⟨X, hsub hX, rfl⟩).trans (le_abs_self M)) hc0) hg)
    exact (hφ _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _).le h1 N) hB)
  refine (norm_setIntegral_le_of_norm_le_const hfin hb).trans (le_of_eq ?_)
  rw [mul_pow (heightConst E n * |M|)]
  ring

private theorem F_left {φ : AdelicGLn.AdelicGL E (r + s) → ℂ} (hφ : IsLeftInvariant φ) (t : ℝ)
    (m : AdelicGLn.AdelicGL E s) :
    IsLeftInvariant fun x : AdelicGLn.AdelicGL E r => constantTerm r φ (lev (Ad E) r s (zt E r t * x, m)) := by
  intro γ x
  have h := Pair.ct_lev_rat hφ γ 1 (zt E r t * x) m
  rw [map_one, one_mul] at h
  have e : zt E r t * (AdelicGLn.diagonal E r γ * x) = AdelicGLn.diagonal E r γ * (zt E r t * x) := by
    rw [← mul_assoc, ← mul_assoc, zt, centralSection_mul_comm]
  beta_reduce
  rw [e, h]

private theorem F_bd (r s N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : AdelicGLn.AdelicGL E (r + s) → ℂ) (B : ℝ), 0 ≤ B →
    (∀ g, ‖φ g‖ ≤ B * AutomorphicForm.height g ^ N) → ∀ (t : ℝ) (m : AdelicGLn.AdelicGL E s)
    (x : AdelicGLn.AdelicGL E r), ‖constantTerm r φ (lev (Ad E) r s (zt E r t * x, m))‖ ≤
      (C * B * Real.exp (((2 * Fintype.card (InfinitePlace E) * N : ℕ) : ℝ) * |t|) * AutomorphicForm.height m ^ N) *
        AutomorphicForm.height x ^ N := by
  obtain ⟨C, hC0, hC⟩ := ct_bd (E := E) (r + s) r N
  have h1 : 0 ≤ heightConst E (r + s) := le_trans zero_le_one one_le_heightConst
  have h2 : 0 ≤ heightConst E r := le_trans zero_le_one one_le_heightConst
  refine ⟨C * (heightConst E (r + s) * heightConst E r) ^ N, by positivity, fun φ B hB hφ t m x => ?_⟩
  have h3 : AutomorphicForm.height (K := E) (lev (Ad E) r s (zt E r t * x, m)) ≤ heightConst E (r + s) *
      (heightConst E r * Real.exp |t| ^ (2 * Fintype.card (InfinitePlace E)) * AutomorphicForm.height x) *
      AutomorphicForm.height m :=
    (Pair.height_lev _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((height_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ht_zt t) h2) (height_pos _).le)) h1) (height_pos _).le)
  refine (hC φ B hB hφ _).trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _).le h3 N)
    (mul_nonneg hC0 hB)).trans_eq ?_)
  rw [Real.exp_nat_mul, pow_mul (Real.exp |t|) _ N]
  simp only [mul_pow]
  ring

variable [_root_.NumberField.IsTotallyComplex E] {S : Set (Pl E)}

private theorem sl_int (b : Blo S r) (φ : Sm E (r + s)) (hφ : Umg φ) (t : ℝ) (m : AdelicGLn.AdelicGL E s) :
    Integrable (fun y : RightCosetSpace (rationalGLOne (K := E) (n := r)) =>
      constantTerm r φ.1 (lev (Ad E) r s (zt E r t * ((Quotient.out y : normOneGL (K := E) (n := r)) : AdelicGLn.AdelicGL E r), m)) *
        starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL (K := E) (n := r)) : AdelicGLn.AdelicGL E r)))
      (quotientMeasure (rationalGLOne (K := E) (n := r)) (mu1 E r)) := by
  have hcφ : Continuous φ.1 := ((umgOps E (r + s)).2 φ hφ).1
  obtain ⟨hfU, hfC⟩ := cuspUmg E r b.f b.cusp
  have hcf : Continuous b.f.1 := ((umgOps E r).2 b.f hfU).1
  obtain ⟨N, hN⟩ := hφ.growth
  obtain ⟨B, hB⟩ := hN 1
  have hB' : ∀ g, ‖φ.1 g‖ ≤ |B| * AutomorphicForm.height g ^ N := fun g =>
    (show ‖φ.1 g‖ ≤ B * AutomorphicForm.height g ^ N by simpa using hB g).trans
      (mul_le_mul_of_nonneg_right (le_abs_self B) (pow_nonneg (height_pos _).le N))
  obtain ⟨C, -, hC⟩ := F_bd (E := E) r s N
  obtain ⟨D, hD⟩ := rapidDecay E r b.f hfU hfC N
  exact Pair.pair_int (F_left hφ.left t m) hfU.left
    ((UpperTheory.continuous_constantTerm E (r + s) r φ.1 hcφ).comp
      (Pair.continuous_lev.comp ((continuous_const.mul continuous_id).prodMk continuous_const))) hcf
    (fun x => hC φ.1 _ (abs_nonneg B) hB' t m x) hD

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW in
theorem UpperTheory.ConvolutionTheory.BW.sliceBound :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.SliceBound E := by
  intro E _ _ _ S r s b
  refine ⟨fun N => ?_, fun φ ψ c hφ hψ t m => ?_⟩
  · obtain ⟨hfU, hfC⟩ := cuspUmg E r b.f b.cusp
    obtain ⟨C, hC0, hC⟩ := F_bd (E := E) r s N
    obtain ⟨D, hD⟩ := rapidDecay E r b.f hfU hfC N
    have hfin := isFiniteMeasure_quotientMeasure (K := E) (n := r) (mu1 E r)
    refine ⟨C * 2 ^ N * D * (quotientMeasure (rationalGLOne (K := E) (n := r)) (mu1 E r)).real Set.univ,
      ((2 * Fintype.card (InfinitePlace E) * N : ℕ) : ℝ), fun φ B hφ hB t m => ?_⟩
    have hB0 : 0 ≤ B := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hB 1)) (pow_pos (height_pos _) N)
    have hm := (height_pos (K := E) m).le
    refine (norm_integral_le_of_norm_le_const (.of_forall fun y =>
      Pair.pair_le (F_left hφ.left t m) (by positivity) (fun x => hC φ.1 B hB0 hB t m x) hD _)).trans_eq ?_
    ring
  · have hcφ : Continuous φ.1 := ((umgOps E (r + s)).2 φ hφ).1
    have hcψ : Continuous ψ.1 := ((umgOps E (r + s)).2 ψ hψ).1
    have e : ∀ g, constantTerm r (c • φ + ψ).1 g = c * constantTerm r φ.1 g + constantTerm r ψ.1 g := fun g => by
      rw [← smul_eq_mul, ← constantTerm_smul, ← constantTerm_add (hcφ.const_smul c) hcψ]
      rfl
    simp only [slice, e, add_mul, mul_assoc c]
    rw [integral_add ((sl_int b φ hφ t m).const_mul c) (sl_int b ψ hψ t m), integral_const_mul]
end
