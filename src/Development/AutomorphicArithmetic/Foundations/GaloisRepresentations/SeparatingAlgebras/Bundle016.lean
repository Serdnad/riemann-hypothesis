module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle243
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle214
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle244
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle219
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle204
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

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem exists_map_eq {α : Type} {a : ℕ} (B : Multiset α) (hB : Multiset.card B = a) :
    ∃ z : Fin a → α, Finset.univ.val.map z = B := by
  obtain ⟨l, rfl⟩ := Quotient.exists_rep B
  have hl : l.length = a := hB
  subst hl
  exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩

theorem UpperTheory.Gal.Gen.globOp_pf :
    UpperTheory.Gal.Gen.LocOp → UpperTheory.Gal.Gen.GlobOp := by
  classical
  intro hLoc E _ _ _ a K w hw hK
  obtain ⟨C, hC⟩ := hLoc E w a
  refine ⟨C, fun p hp => ?_⟩
  obtain ⟨h, hdist, hsum, hact⟩ := hC p hp
  let zf : SmIrr (GL (Fin a) (w.adicCompletion E)) → ℂ := fun σ =>
    if hz : ∃ z : Fin a → ℂˣ, GlobalTheory.LFun.HasSatGL w σ.ρ (Finset.univ.val.map z) then evalAt hz.choose p else 0
  have hop : ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), ∀ v ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w (n := a)),
      opOf σ.ρ h v = zf σ • v := by
    intro σ v hv
    by_cases hv0 : v = 0
    · subst hv0
      simp [opOf]
    · obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred
        ((Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩)
      obtain ⟨z, rfl⟩ := exists_map_eq B (GlobalTheory.LFun.HasSatGL.card hB)
      have hz : ∃ z : Fin a → ℂˣ, GlobalTheory.LFun.HasSatGL w σ.ρ (Finset.univ.val.map z) := ⟨z, hB⟩
      have hzf : zf σ = evalAt hz.choose p := dif_pos hz
      rw [hzf]
      exact hact σ _ hz.choose_spec v hv
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w a
  obtain ⟨h', hsup, hU⟩ := GlobalTheory.T.localOperator_acts_by_localComponentScalar E a w hw (GlobalTheory.LFun.KGL w (n := a)) hKc hKo h zf hop
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  have hinj : ∀ g ∈ locU a w, ∀ g' ∈ locU a w, cLoc w g = cLoc w g' → g = g' := by
    intro g hg g' hg' hgg
    have : (⟨g, hg⟩ : locU a w) = ⟨g', hg'⟩ := e.injective (by rw [he, he]; exact hgg)
    exact congrArg Subtype.val this
  have hmem : ∀ g ∈ h'.support, cLoc w g ∈ h.support := by
    intro g hg
    rw [Finsupp.mem_support_iff, ← (hsup g hg).2]
    exact Finsupp.mem_support_iff.1 hg
  refine ⟨h', fun g hg => (hsup g hg).1, ?_, ?_, ?_⟩
  · intro g hg g' hg' hgK
    have hl : g⁻¹ * g' ∈ locU a w := (locU a w).mul_mem ((locU a w).inv_mem (hsup g hg).1) (hsup g' hg').1
    have hk := (hK _ hl).1 hgK
    rw [map_mul, map_inv] at hk
    exact hinj g (hsup g hg).1 g' (hsup g' hg').1 (hdist _ (hmem g hg) _ (hmem g' hg') hk)
  · refine le_trans ?_ hsum
    have h1 : ∑ g ∈ h'.support, ‖h' g‖ ^ 2 = ∑ x ∈ h'.support.image (cLoc w), ‖h x‖ ^ 2 := by
      rw [Finset.sum_image fun g hg g' hg' hgg => hinj g (hsup g hg).1 g' (hsup g' hg').1 hgg]
      exact Finset.sum_congr rfl fun g hg => by rw [(hsup g hg).2]
    rw [h1]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    exact hmem g hg
  · rintro U hUa z ⟨σ, hcomp, hsat⟩ φ hφ hfix
    rw [hU U hUa σ hcomp φ hφ fun x hx hk => hfix x ((hK x hx).2 hk)]
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hsat.1
    have h1 := hop σ v hv
    rw [hact σ z hsat v hv] at h1
    rw [smul_left_injective ℂ hv0 h1]
end

section

open NumberField IsDedekindDomain
open Neutral.B1 hiding G
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.toPolyX_pf :
    UpperTheory.Gal.Gen.PartFacts → UpperTheory.Gal.Gen.ToPolyX := by
  intro hPF E _ _ _ l _ ι a w₀ K hK lam P hD Jx t η hFr hact U hU ε hε
  classical
  obtain ⟨W, f, hW, hf0, hfU, hfK, -⟩ := GlobalTheory.T.exists_algebraicForm_weight_level_smooth_at_place E a lam K U hK hU w₀
  have hWe : Wt.ofFam lam = W := funext fun v => by
    show lam v.embedding = W v
    rw [← hW, Wt.at_embedding]
  rw [hWe] at hD hFr
  obtain ⟨X, b, hbd, hdef, hne⟩ := hFr
  obtain ⟨g₀, i₀, hz⟩ : ∃ g i, f.1 (b g i) g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (hdef f h)
  set z₀ := f.1 (b g₀ i₀) g₀ with hz₀
  let f₁ : algForms W := z₀⁻¹ • f
  have hf₁ : ∀ v g, f₁.1 v g = z₀⁻¹ * f.1 v g := fun v g => rfl
  have hf₁K : f₁ ∈ fixedBy W K := fun k hk v g => by rw [hf₁, hf₁, hfK k hk v g]
  have hf₁U : ∀ v, f₁.1 v ∈ U := fun v => U.smul_mem _ (hfU v)
  obtain ⟨R₀, hR₀⟩ := hbd f₁
  set R := max R₀ 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hR : ∀ g i, ‖ι.symm (f₁.1 (b g i) g)‖ ≤ R := fun g i => (hR₀ g i).trans (le_max_left _ _)
  obtain ⟨G, hG, e, he, hfe⟩ := hD f₁ hf₁K (ε / R) (div_pos hε hRpos)
  obtain ⟨I, F, hI, hsum⟩ := (hPF E a W K P).2.2.2.2 G hG
  let T : Jx → Module.End ℂ (W.Sp →ₗ[ℂ] (UA E a → ℂ)) := fun j =>
    LinearMap.llcomp ℂ W.Sp (UA E a → ℂ) (UA E a → ℂ) (GlobalTheory.CongSc.opL (t j))
  let ev : UA E a × X → (W.Sp →ₗ[ℂ] (UA E a → ℂ)) →ₗ[ℂ] ℂ := fun x =>
    (LinearMap.proj x.1) ∘ₗ (LinearMap.applyₗ (b x.1 x.2))
  have hT : ∀ j (F' : W.Sp →ₗ[ℂ] (UA E a → ℂ)) v, T j F' v = opOf (RU E a) (t j) (F' v) := fun _ _ _ => rfl
  have hev : ∀ x (F' : W.Sp →ₗ[ℂ] (UA E a → ℂ)), ev x F' = F' (b x.1 x.2) x.1 := fun _ _ => rfl
  have hne' : ∀ (F' : W.Sp →ₗ[ℂ] (UA E a → ℂ)) (R' : ℝ), (∀ x, ‖ι.symm (ev x F')‖ ≤ R') →
      ∀ j x, ‖ι.symm (ev x (T j F'))‖ ≤ R' := fun F' R' hR' j x =>
    hne F' R' (fun g i => hR' (g, i)) j x.1 x.2
  have heig0 : ∀ j, T j f₁.1 = η U j • f₁.1 := by
    intro j; apply LinearMap.ext; intro v
    rw [hT, LinearMap.smul_apply]
    exact hact U hU.aut (f₁.1 v) (hf₁U v) (fun x hx => funext fun g => hf₁K x hx v g) j
  have hnorm : ‖ι.symm (ev (g₀, i₀) f₁.1)‖ = 1 := by
    have : ev (g₀, i₀) f₁.1 = 1 := by
      rw [hev]
      show z₀⁻¹ * f.1 (b g₀ i₀) g₀ = 1
      exact inv_mul_cancel₀ hz
    rw [this, map_one, norm_one]
  let vv : ↥I → (W.Sp →ₗ[ℂ] (UA E a → ℂ)) := fun π => -(F π.1).1
  let η' : ↥I → Jx → ℂ := fun π => η π.1.V
  have heig : ∀ π j, T j (vv π) = η' π j • vv π := by
    rintro ⟨π, hπ⟩ j
    obtain ⟨-, hfin, hfix, -⟩ := hI π hπ
    have h : T j (F π).1 = η π.V j • (F π).1 := by
      apply LinearMap.ext; intro v
      rw [hT, LinearMap.smul_apply]
      exact hact π.V π.isAut _ (AutSub.mem_finPart.1 hfin v)
        (fun x hx => funext fun g => hfix x hx v g) j
    show T j (-(F π).1) = η π.V j • -(F π).1
    rw [map_neg, h, smul_neg]
  have hvsum : f₁.1 + ∑ π, vv π = f₁.1 - G.1 := by
    have h1 : ∑ π, vv π = -G.1 := by
      simp only [vv]
      rw [Finset.sum_neg_distrib, Finset.sum_coe_sort I (fun π => (F π).1), hsum, Submodule.coe_sum]
    rw [h1, sub_eq_add_neg]
  have hbound : ∀ x, ‖ι.symm (ev x (f₁.1 + ∑ π, vv π))‖ ≤ ε := by
    intro x
    have h1 : ev x (f₁.1 + ∑ π, vv π) = e x.1 * f₁.1 (b x.1 x.2) x.1 := by
      rw [hvsum, hev]
      exact hfe _ _
    rw [h1, map_mul, norm_mul]
    calc ‖ι.symm (e x.1)‖ * ‖ι.symm (f₁.1 (b x.1 x.2) x.1)‖ ≤ ε / R * R :=
          mul_le_mul (he _) (hR _ _) (norm_nonneg _) (div_pos hε hRpos).le
      _ = ε := div_mul_cancel₀ _ hRpos.ne'
  obtain ⟨s, c, hs, hP⟩ := GlobalTheory.T.eigenvector_small_sub_finite_eigen_approx_inequality l ι (W.Sp →ₗ[ℂ] (UA E a → ℂ)) (UA E a × X) Jx
    ↥I T ev hne' f₁.1 (η U) (g₀, i₀) heig0 hnorm vv η' heig ε hbound
  refine ⟨s, c, ?_, hP⟩
  intro z hz'
  obtain ⟨⟨π, hπ⟩, rfl⟩ := hs z hz'
  obtain ⟨hPπ, hfin, hfix, hF0⟩ := hI π hπ
  refine ⟨π.V, ?_, hPπ, rfl⟩
  have h := GlobalTheory.T.isAutomorphicOfWeight_of_nonzero_fixed_finPart_form E a π W K (F π) hfin hF0 (fun k hk v g => hfix k hk v g)
  have hl' : (fun τ => W.at τ) = lam := funext hW
  rwa [hl'] at h
end
