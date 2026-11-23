module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveDualWeylTensorCuspFormsRationalPo
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
public import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag

@[expose] public section

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.PureStabOne

theorem pure_stab_one : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ g ∈ UAt σ G.V' (evFin F v), ∀ h ∈ UAt σ G.W (evFin F v),
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ φ' : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ w, φ' w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧
      (∀ w, w ≠ v → φ' w = φ w) ∧ Acts (evFin F v) (om' (g, h)) (φ v) (φ' v) ∧ om' (g, h) (pure f φ) = pure f φ' := by
  classical
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v g hg h hh f φ hSB hvac
  have hpair := GlobalTheory.ThK.Inhab.pairV' hT
  obtain ⟨φ₁, ⟨hφ₁SB, hAct⟩, -⟩ :=
    ((GlobalTheory.T.theta_action_exists hP) F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hpair v).1 g hg h hh (φ v) (hSB v)
  have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hvac, hT.geo.hM'.std] with w h1 h2
    rw [h1, h2]
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  refine ⟨Function.update φ v φ₁, fun w => ?_, fun w hw => Function.update_of_ne hw _ _, ?_, ?_⟩
  · by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ₁SB
    · rw [Function.update_of_ne hw]; exact hSB w
  · rw [Function.update_self]; exact hAct
  · have e1 : pure f φ = tens (evFin F v) (φ v) r := by rw [hrt, Function.update_eq_self]
    have hRest : Rest (evFin F v) (φ v) r := ⟨hr, by rw [← e1]; exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
    rw [e1, hAct r hRest, hrt]

end GlobalTheory.PureStabOne

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblScalBox

open Matrix

section Local

variable {F : Type} [Field F] [NumberField F]

theorem box_mem_SB {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem conj_mem_SB {Y : Type} [TopologicalSpace Y] {φ : Y → ℂ} (h : φ ∈ SB Y) :
    (fun y => starRingEnd ℂ (φ y)) ∈ SB Y :=
  ⟨h.1.comp _, h.2.comp_left (map_zero _)⟩

theorem tens_box (v : Pl (F := F)) {κ κ' : Type} (φ₁ : (κ → Fv F v) → ℂ) (φ₂ : (κ' → Fv F v) → ℂ)
    (r₁ : (κ → AF F) → ℂ) (r₂ : (κ' → AF F) → ℂ) :
    tens (evFin F v) (boxFun φ₁ φ₂) (boxFun r₁ r₂) = boxFun (tens (evFin F v) φ₁ r₁) (tens (evFin F v) φ₂ r₂) := by
  funext x
  simp only [tens, boxFun, Function.comp_def]
  ring

theorem rest_box (v : Pl (F := F)) {κ κ' : Type} [Fintype κ] [Fintype κ'] {φ₁ : (κ → Fv F v) → ℂ} {φ₂ : (κ' → Fv F v) → ℂ}
    {r₁ : (κ → AF F) → ℂ} {r₂ : (κ' → AF F) → ℂ} (h₁ : Rest (evFin F v) φ₁ r₁) (h₂ : Rest (evFin F v) φ₂ r₂) :
    Rest (evFin F v) (boxFun φ₁ φ₂) (boxFun r₁ r₂) := by
  refine ⟨fun x z hz => ?_, ?_⟩
  · have hz1 : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
      funext i; exact congrFun (hz u hu) (Sum.inl i)
    have hz2 : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
      funext i; exact congrFun (hz u hu) (Sum.inr i)
    show r₁ ((x + z) ∘ Sum.inl) * r₂ ((x + z) ∘ Sum.inr) = r₁ (x ∘ Sum.inl) * r₂ (x ∘ Sum.inr)
    rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
      show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, h₁.1 _ _ hz1, h₂.1 _ _ hz2]
  · rw [tens_box]
    exact GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ h₁.2 _ h₂.2

theorem eq_of_tens_ne (v : Pl (F := F)) {κ : Type} {ψ₁ ψ₂ : (κ → Fv F v) → ℂ} {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) {x₀ : κ → AF F} (h0 : r x₀ ≠ 0)
    (h : tens (evFin F v) ψ₁ r = tens (evFin F v) ψ₂ r) : ψ₁ = ψ₂ := by
  funext y
  let z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x₀ i))
  have hz : At (evFin F v) z := by
    intro u hu; funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hev : (fun i => evFin F v ((x₀ + z) i)) = y := by
    funext i
    simp only [Pi.add_apply, z, map_add (f := _), GlobalTheory.LatVac.evFin_liftV]
    abel
  have e := congrFun h (x₀ + z)
  simp only [tens, hev, hr x₀ z hz] at e
  exact mul_right_cancel₀ h0 e

end Local

theorem scal_diag_one : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ W.J → ℂ, (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = κ h • fun Y => ι φ (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val)) →
    ∀ (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
      (∀ (g : UA σ W.J) (gd : GlobalTheory.DblScal.UD σ W.J),
        ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
          Matrix.fromBlocks (mat g) 0 0 1 →
        ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), omd gd (boxFun φ₁ φ₂) = boxFun (om (1, g) φ₁) φ₂) →
      GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd →
      (∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v),
        ιd (boxFun φ₁ φ₂) = fun Y => ι φ₁ (Y.submatrix id Sum.inl) *
          starRingEnd ℂ (ι (fun x => starRingEnd ℂ (φ₂ x)) (Y.submatrix id Sum.inr))) →
      ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∀ h ∈ UAt σ W (evFin F v), ∀ gd : GlobalTheory.DblScal.UD σ W.J,
        ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
          Matrix.fromBlocks (mat h) 0 0 1 → κ h = cd gd := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair v t b c ι hι κ hκ dd omd hdd hspl hres hloc ιd hιd hbox cd
    hcd h hh gd hgd
  have hιL : M.IsLin B.ψ (piW t) (piW (t.comp σ)) (fun u => (b⁻¹).1 * u.map (piW t) * (c⁻¹).1ᵀ) ι := hι

  set φ₀ : (Fin n × Fin d → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 with hφ₀def
  have h0 : φ₀ ∈ SB (Fin n × Fin d → Fv F v) := GlobalTheory.StdVacuum.indicator_mem_SB v
  have hφ₀0 : φ₀ (fun _ => 0) = 1 := by
    rw [hφ₀def, Set.indicator_of_mem (show (fun _ => (0 : Fv F v)) ∈
      {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun i => zero_mem _)]
    rfl
  have hne : ι φ₀ ≠ 0 := by
    intro e
    have e0 : φ₀ = 0 := hιL.bij.injOn h0 (SB _).zero_mem (by rw [e, map_zero])
    have e1 := congrFun e0 (fun _ => 0)
    rw [hφ₀0] at e1
    exact one_ne_zero e1
  obtain ⟨Y₀, hY₀⟩ : ∃ Y, ι φ₀ Y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  set φ₂ : (Fin n × Fin d → Fv F v) → ℂ := fun x => starRingEnd ℂ (φ₀ x) with hφ₂def
  have h2 : φ₂ ∈ SB (Fin n × Fin d → Fv F v) := conj_mem_SB h0
  have hcc : (fun x => starRingEnd ℂ (φ₂ x)) = φ₀ := funext fun x => Complex.conj_conj _

  have h1mem : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
    intro u _
    have e : mat (1 : UA σ X.J) = 1 := rfl
    rw [e, sub_self, smul_zero]
  obtain ⟨φ₁, ⟨h1, hA1⟩, -⟩ := (GlobalTheory.T.theta_action_exists hP F E σ B n d X W M χX χW om r s r' s' hPair v).1 1 h1mem h hh φ₀ h0
  have hk := hκ h hh φ₀ h0 φ₁ h1 hA1

  have hgdAt : gd ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v) := by
    intro u hu
    rw [hgd, GlobalTheory.DblScal.fromBlocks_sub_one, Matrix.fromBlocks_smul, hh u hu]
    simp
  obtain ⟨Φ₁, hΦ₁, hAd⟩ := hloc gd hgdAt (boxFun φ₀ φ₂) (box_mem_SB h0 h2)
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin n × Fin d) v
  have hRb := rest_box v (hR φ₀ h0) (hR φ₂ h2)
  have e := hAd _ hRb
  rw [tens_box, hres h gd hgd _ (hR φ₀ h0).2 _ (hR φ₂ h2).2, hA1 R (hR φ₀ h0), ← tens_box] at e
  have h0r : boxFun R R (0 : Fin n × Fin d ⊕ Fin n × Fin d → AF F) ≠ 0 := by
    show R 0 * R 0 ≠ 0
    exact mul_ne_zero hR0 hR0
  have eΦ : Φ₁ = boxFun φ₁ φ₂ := eq_of_tens_ne v hRb.1 h0r e.symm

  have hs := hcd gd hgdAt (boxFun φ₀ φ₂) (box_mem_SB h0 h2) Φ₁ hΦ₁ hAd
  rw [eΦ] at hs
  set L := locMat t c h with hL
  have hD : (GlobalTheory.DblScal.locMatD t c gd).val = Matrix.fromBlocks L.val 0 0 1 := by
    show ((GlobalTheory.DblScal.dsum c)⁻¹).val * (((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix _ _ _).map (piW t)) *
      (GlobalTheory.DblScal.dsum c).val = _
    rw [hgd, hL, locMat_val, fromBlocks_map]
    simp only [GlobalTheory.DblScal.dsum, Units.inv_mk, fromBlocks_multiply, Matrix.map_zero _ (map_zero (piW t)),
      Matrix.map_one _ (map_zero (piW t)) (map_one (piW t)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Matrix.mul_one, Matrix.one_mul]
    congr 1
    simp [Units.mul_inv]
  have hDinv : ((GlobalTheory.DblScal.locMatD t c gd)⁻¹).val = Matrix.fromBlocks (L⁻¹).val 0 0 1 := by
    have hm : Matrix.fromBlocks (L⁻¹).val 0 0 1 * (GlobalTheory.DblScal.locMatD t c gd).val = 1 := by
      rw [hD, fromBlocks_multiply]
      simp [← fromBlocks_one]
    calc ((GlobalTheory.DblScal.locMatD t c gd)⁻¹).val
        = (Matrix.fromBlocks (L⁻¹).val 0 0 1 * (GlobalTheory.DblScal.locMatD t c gd).val) *
            ((GlobalTheory.DblScal.locMatD t c gd)⁻¹).val := by rw [hm, Matrix.one_mul]
      _ = Matrix.fromBlocks (L⁻¹).val 0 0 1 := by
          rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hT : (GlobalTheory.SplitFlip.invT (GlobalTheory.DblScal.locMatD t c gd)).val =
      Matrix.fromBlocks (GlobalTheory.SplitFlip.invT L).val 0 0 1 := by
    rw [GlobalTheory.SplitFlip.invT_val, GlobalTheory.SplitFlip.invT_val, hDinv, fromBlocks_transpose]
    simp
  have hY : Y₀ * L.valᵀ * (GlobalTheory.SplitFlip.invT L).val = Y₀ := by
    rw [GlobalTheory.SplitFlip.invT_val, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
      Matrix.mul_one]
  have hsl : ∀ A Bm : Matrix (Fin n) (Fin d) (Fv F v), (Matrix.fromCols A Bm).submatrix id Sum.inl = A := by
    intro A Bm; ext i j; rfl
  have hsr : ∀ A Bm : Matrix (Fin n) (Fin d) (Fv F v), (Matrix.fromCols A Bm).submatrix id Sum.inr = Bm := by
    intro A Bm; ext i j; rfl
  have hmul : Matrix.fromCols (Y₀ * L.valᵀ) Y₀ * (GlobalTheory.SplitFlip.invT (GlobalTheory.DblScal.locMatD t c gd)).val =
      Matrix.fromCols Y₀ Y₀ := by
    rw [hT, Matrix.fromCols_mul_fromBlocks]
    simp [hY]
  have eY := congrFun hs (Matrix.fromCols (Y₀ * L.valᵀ) Y₀)
  rw [hbox φ₁ h1 φ₂ h2, Pi.smul_apply, smul_eq_mul, hmul, hbox φ₀ h0 φ₂ h2] at eY
  simp only [hsl, hsr, hcc, hk, Pi.smul_apply, smul_eq_mul, hY] at eY
  have hP0 : ι φ₀ Y₀ * starRingEnd ℂ (ι φ₀ Y₀) ≠ 0 := mul_ne_zero hY₀ ((map_ne_zero _).mpr hY₀)
  apply mul_right_cancel₀ hP0
  linear_combination eY

end GlobalTheory.DblScalBox

end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SchurCharV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem two_ne_zero_Fv (v : Pl (F := F)) : (2 : Fv F v) ≠ 0 := by
  have h := (algebraMap F (Fv F v)).injective.ne (two_ne_zero (α := F))
  rwa [map_ofNat, map_zero] at h

theorem eq_liftU_of_UAt {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {n : ℕ}
    (X : Spc F E n) (herm : ∀ i j, σ (X.J j i) = algebraMap F E 1 * X.J i j) (hJ : IsUnit (X.J.map t).det)
    (g : UA σ X.J) (hg : g ∈ UAt σ X (evFin F v)) :
    g = GlobalTheory.SplitUnitLift.liftU h t X.J 1 herm hJ (Matrix.GeneralLinearGroup.map (piW t) g.1) := by
  set g' := Matrix.GeneralLinearGroup.map (piW t) g.1 with hg'
  have hv : g'.val = (mat g).map (piW t) := rfl
  set L := GlobalTheory.SplitUnitLift.liftU h t X.J 1 herm hJ g' with hL
  have hU : (mat g)ᵀ * incM F X.J * (mat g).map (cA σ) = incM F X.J := g.2
  have tr : ∀ (A B C : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      (Aᵀ * B * C).map (piW t) = (A.map (piW t))ᵀ * B.map (piW t) * C.map (piW t) := fun A B C => by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hJm : (incM F X.J).map (piW t) = X.J.map t := by
    unfold incM
    rw [Matrix.map_map]
    exact Matrix.ext fun i j => GlobalTheory.SplitGLLift.piW_inclR t (X.J i j)
  have hcm : ((mat g).map (cA σ)).map (piW t) = (mat g).map (piW (t.comp σ)) := by
    rw [Matrix.map_map]
    exact Matrix.ext fun i j => GlobalTheory.VacIso.piW_cA σ t _
  have hUt : ((mat g)ᵀ * incM F X.J * (mat g).map (cA σ)).map (piW t) = (incM F X.J).map (piW t) := by rw [hU]
  rw [tr, hJm, hcm, ← hv] at hUt
  set gs := (mat g).map (piW (t.comp σ)) with hgs
  have hσ : gs = (X.J.map t)⁻¹ * ((g'⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ * X.J.map t := by
    have e : gs = ((X.J.map t)⁻¹ * ((g'⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ) * ((g'.val)ᵀ * X.J.map t * gs) := by
      rw [show ((X.J.map t)⁻¹ * ((g'⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ) * ((g'.val)ᵀ * X.J.map t * gs) =
          (X.J.map t)⁻¹ * (((g'⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ * (g'.val)ᵀ) * X.J.map t * gs by
            simp only [Matrix.mul_assoc],
        ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one,
        Matrix.nonsing_inv_mul _ hJ, Matrix.one_mul]
    rw [e, hUt]
  have hgA : At (evFin F v) (mat g - 1) := hg
  have hLA : At (evFin F v) (mat L - 1) := GlobalTheory.SplitUnitLift.liftU_mem_UAt h t X 1 herm hJ g'
  have hLt : (mat L).map (piW t) = g'.val := GlobalTheory.SplitUnitLift.liftU_piW h t X.J 1 herm hJ g'
  have hLs : (mat L).map (piW (t.comp σ)) = (X.J.map t)⁻¹ * ((g'⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ * X.J.map t :=
    GlobalTheory.SplitUnitLift.liftU_piW_comp h t X.J 1 herm hJ g'
  apply Subtype.ext
  apply Units.ext
  show mat g = mat L
  ext i j
  rw [← sub_eq_zero]
  have hz : mat g i j - mat L i j = (mat g - 1) i j - (mat L - 1) i j := by
    simp only [Matrix.sub_apply]; ring
  refine GlobalTheory.VacIso.eq_zero_of_at_split h t ?_ ?_ ?_
  · intro u hu
    have e1 := congrFun (congrFun (hgA u hu) i) j
    have e2 := congrFun (congrFun (hLA u hu) i) j
    simp only [Matrix.smul_apply, Matrix.zero_apply] at e1 e2
    rw [hz, smul_sub, e1, e2, sub_zero]
  · have e1 := congrFun (congrFun hLt i) j
    have e2 := congrFun (congrFun hv i) j
    simp only [Matrix.map_apply] at e1 e2
    rw [map_sub, e1, ← e2, sub_self]
  · have e1 := congrFun (congrFun hLs i) j
    have e2 := congrFun (congrFun hσ i) j
    simp only [hgs, Matrix.map_apply] at e1 e2
    rw [map_sub, e1, e2, sub_self]

end GlobalTheory.SchurCharV


open GlobalTheory.SchurCharV in
theorem GlobalTheory.SchurCharV.exists_char_of_schur : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ g ∈ UAt σ G.V (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (((mat g).map (piW t))⁻¹ * Y)) →
    ∃ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ 1 g' 1 (ι φ)) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v _ t ι hι H
  have hcm : IsCMExt F E σ := hT.base.cm
  have herm : ∀ i j, σ (G.V.J j i) = algebraMap F E 1 * G.V.J i j := fun i j => by
    rw [map_one, one_mul]; exact hT.geo.hV.herm i j
  have hJ : IsUnit (G.V.J.map t).det := by
    have w := Classical.arbitrary (InfinitePlace F)
    exact GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V.J t (B.emb w).1 1 one_ne_zero (G.V.θ w)
      (by rw [one_smul]; exact hT.geo.hV.cartan w)
  set L := GlobalTheory.SplitUnitLift.liftU hcm t G.V.J 1 herm hJ with hLdef
  have hLmem : ∀ x, L x ∈ UAt σ G.V (evFin F v) := fun x => GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.V 1 herm hJ x
  have hLt : ∀ x, (mat (L x)).map (piW t) = x.val := fun x => GlobalTheory.SplitUnitLift.liftU_piW hcm t G.V.J 1 herm hJ x
  have hEx := (GlobalTheory.T.theta_action_exists hP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1 v).1
  have h1mem : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := by
    intro u _
    show u • (mat (1 : UA σ G.W.J) - 1) = 0
    rw [show mat (1 : UA σ G.W.J) = 1 from rfl, sub_self, smul_zero]
  have hpres : ∀ p : UA σ G.V.J × UA σ G.W.J, ∀ Φ ∈ schA F (Fin a × Fin (a + a')),
      om p Φ ∈ schA F (Fin a × Fin (a + a')) :=
    fun p Φ hΦ => (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil).pres p Φ hΦ
  have hvac := hT.geo.hM.vac v
  set φv := G.M.vac v
  have hφv : φv ∈ SB (Fin a × Fin (a + a') → Fv F v) := hvac.1
  have hbij := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι
  have hιv : ι φv ≠ 0 := fun h0 => hvac.2.1 (hbij.injOn hφv (Submodule.zero_mem _) (by rw [h0, map_zero]))
  obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.mp hιv
  choose c hc using fun x : GL (Fin a) (Fv F v) => H (L x) (hLmem x)
  have hrel : ∀ x, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (L x, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c x * ι φ ((x⁻¹ : GL (Fin a) (Fv F v)).val * Y) := by
    intro x φ hφ φ₁ hφ₁ hA Y
    rw [hc x φ hφ φ₁ hφ₁ hA Y, hLt x, Matrix.coe_units_inv]
  have hmul : ∀ x y, c (x * y) = c x * c y := by
    intro x y
    obtain ⟨φ₂, ⟨hφ₂, hA₂⟩, -⟩ := hEx (L y) (hLmem y) 1 h1mem φv hφv
    obtain ⟨φ₃, ⟨hφ₃, hA₃⟩, -⟩ := hEx (L x) (hLmem x) 1 h1mem φ₂ hφ₂
    have hA : Acts (evFin F v) (om (L (x * y), 1)) φv φ₃ := by
      have e : ((L (x * y), 1) : UA σ G.V.J × UA σ G.W.J) = (L x, 1) * (L y, 1) := by
        rw [Prod.mk_mul_mk, map_mul, one_mul]
      rw [e, map_mul]
      exact GlobalTheory.InertAvgDual.acts_comp v _ _ (hpres _) hA₂ hA₃
    have e1 := hrel (x * y) φv hφv φ₃ hφ₃ hA ((x * y).val * Y₀)
    have e2 := hrel x φ₂ hφ₂ φ₃ hφ₃ hA₃ ((x * y).val * Y₀)
    have e3 := hrel y φv hφv φ₂ hφ₂ hA₂ (y.val * Y₀)
    have k1 : ((x * y)⁻¹ : GL (Fin a) (Fv F v)).val * ((x * y).val * Y₀) = Y₀ := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    have k2 : (x⁻¹ : GL (Fin a) (Fv F v)).val * ((x * y).val * Y₀) = y.val * Y₀ := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel_left]
    have k3 : (y⁻¹ : GL (Fin a) (Fv F v)).val * (y.val * Y₀) = Y₀ := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    rw [k1] at e1
    rw [k2] at e2
    rw [k3] at e3
    rw [e2, e3] at e1
    exact mul_right_cancel₀ hY₀ (e1.symm.trans (mul_assoc _ _ _).symm)
  have hone : c 1 = 1 := by
    have hA : Acts (evFin F v) (om (L 1, 1)) φv φv := by
      rw [map_one, show ((1 : UA σ G.V.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one]
      exact GlobalTheory.InertAvgDual.acts_one v φv
    have e := hrel 1 φv hφv φv hφv hA Y₀
    rw [inv_one, Units.val_one, Matrix.one_mul] at e
    exact (mul_eq_right₀ hY₀).mp e.symm
  let cH : GL (Fin a) (Fv F v) →* ℂ := ⟨⟨c, hone⟩, hmul⟩
  obtain ⟨χ, hχ⟩ := GlobalTheory.ghom_factors_through_det (two_ne_zero_Fv v) cH.toHomUnits
  have hcχ : ∀ x, c x = (χ (Matrix.GeneralLinearGroup.det x) : ℂ) := fun x => by rw [← hχ x]; rfl
  let A : (Fv F v)ˣ →* ℂˣ :=
    { toFun := fun x => Units.mk0 (GlobalTheory.SplitFlip.apow x (((a + a' : ℕ) : ℂ) / 2)) (GlobalTheory.SplitFlip.apow_ne_zero _ _)
      map_one' := Units.ext (GlobalTheory.SplitFlip.apow_one _)
      map_mul' := fun x y => Units.ext (GlobalTheory.SplitFlip.apow_mul x y _) }
  refine ⟨(χ * A)⁻¹, ?_⟩
  intro g hg
  set g' := Matrix.GeneralLinearGroup.map (piW t) g.1 with hg'
  refine ⟨g', rfl, ?_⟩
  intro φ hφ φ₁ hφ₁ hA
  have hgL : g = L g' := eq_liftU_of_UAt hcm t G.V herm hJ g hg
  rw [hgL] at hA
  funext Y
  rw [hrel g' φ hφ φ₁ hφ₁ hA Y, hcχ g']
  have hpow : ∀ d : (Fv F v)ˣ, GlobalTheory.SplitFlip.apow d (((a + a' : ℕ) : ℂ) / 2) *
      GlobalTheory.SplitFlip.apow d (-((a + a' : ℕ) : ℂ) / 2) = 1 := fun d => by
    rw [← GlobalTheory.SplitFlip.apow_add, show ((a + a' : ℕ) : ℂ) / 2 + -((a + a' : ℕ) : ℂ) / 2 = 0 by ring,
      GlobalTheory.SplitFlip.apow_zero]
  simp only [GlobalTheory.SplitFlip.omA, MonoidHom.inv_apply, inv_inv, MonoidHom.mul_apply, Units.val_mul, map_one,
    MonoidHom.one_apply, Units.val_one, GlobalTheory.SplitFlip.apow_one, Matrix.mul_one, mul_one, Fintype.card_fin]
  have hAv : ∀ d, ((A d : ℂˣ) : ℂ) = GlobalTheory.SplitFlip.apow d (((a + a' : ℕ) : ℂ) / 2) := fun d => rfl
  rw [hAv]
  linear_combination (-(χ (GlobalTheory.SplitFlip.gdet g') : ℂ) * ι φ ((g'⁻¹ : GL (Fin a) (Fv F v)).val * Y)) * hpow (GlobalTheory.SplitFlip.gdet g')
end
end

section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

theorem _root_.GlobalTheory.T.exists_injective_dualWeylTensor_cuspForms_rationalPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), DefCase U ξ → Dom a n → ∀ (Z : Comp Xo c) (P : PtData Z), ∃ φ : (TIdx (part Dw a) → c.F) →ₗ[c.F] Rul Xo c, Function.Injective φ ∧ LinearMap.range φ = cuspOn U Z (wtZ a n) ∧ ∀ x, Reads Z P.y₀ a n x (φ x) := by
  first | exact @GlobalTheory.DefPt.ReadsPt.exists_linearMap_reads | exact GlobalTheory.DefPt.ReadsPt.exists_linearMap_reads | (intros; apply GlobalTheory.DefPt.ReadsPt.exists_linearMap_reads <;> assumption)
end

section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.isLinearSystemRatioOfDegree_of_generatesByRatios : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω), GenRatios ev → ∀ (τ : ℕ) (t : Ω), IsRatio ev τ t := by
  first | exact @GlobalTheory.DegVal.isRatio_of_genRatios | exact GlobalTheory.DegVal.isRatio_of_genRatios | (intros; apply GlobalTheory.DegVal.isRatio_of_genRatios <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.card_le_mul_of_unipotent_cover_discreteSubgroup : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ Γ Q : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M) (μ : Measure G) (D V W : Set G), SemiLat N M Λ ν π DN DM → Λ ≤ Γ → Λ ≤ Q → IsClosed (Q : Set G) → (∀ q ∈ Q, ∃ u ∈ N, ∃ x ∈ M, q = u * x) → (∀ K : Set G, IsCompact K → (K ∩ Γ).Finite) → μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → IsCompact V → IsCompact W → ∃ B : ℝ, 0 ≤ B ∧ ∀ (a : G) (Y T : Finset G), (∀ x ∈ M, a * x = x * a) → (∀ u, u ∈ N ↔ a⁻¹ * u * a ∈ N) → (∀ y ∈ Y, y ∈ N) → (∀ u ∈ N, ∃ γ ∈ Λ, γ ∈ N ∧ ∃ y ∈ Y, ∃ w ∈ V, γ * u = y * a * w * a⁻¹) → (∀ t ∈ T, t ∈ Γ) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ Λ → t = t') → (∀ t ∈ T, ∃ q ∈ Q, ∃ w ∈ W, t = q * a * w) → (T.card : ℝ) ≤ B * Y.card := by
  first | exact @GlobalTheory.SphEis.card_le_mul_of_unip_cover | exact GlobalTheory.SphEis.card_le_mul_of_unip_cover | (intros; apply GlobalTheory.SphEis.card_le_mul_of_unip_cover <;> assumption)
end
