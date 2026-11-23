module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
public import GroundTheory.AutomorphicForms.L2LocalComponents.Summand
public import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle005

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.trDual :
    UpperTheory.V.Af.StrongMultiplicityOne.TrDual := by
  classical
  intro E _ _
  let B : LinearMap.BilinForm ℝ (Cinf E) := (LinearMap.mul ℝ (Cinf E)).compr₂ (TG.tr E)
  have hl : ∀ x : Cinf E, (∀ y, B x y = 0) → x = 0 := fun x h => by
    have h1 : ∑ w, 2 * (x w * starRingEnd ℂ (x w)).re = 0 := h fun w => starRingEnd ℂ (x w)
    simp only [Complex.mul_conj, Complex.ofReal_re] at h1
    have b' := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => mul_nonneg zero_le_two (Complex.normSq_nonneg (x w))).1 h1
    exact funext fun w => Complex.normSq_eq_zero.1 ((mul_eq_zero.1 (b' w (Finset.mem_univ _))).resolve_left two_ne_zero)
  have hB : B.Nondegenerate := ⟨hl, fun x h => hl x fun y => by
    have := h y
    change TG.tr E (_ * _) = 0 at this ⊢
    rwa [mul_comm]⟩
  let b := Module.finBasis ℝ (Cinf E)
  refine ⟨_, b, B.dualBasis hB b, fun x y => ?_⟩
  conv_lhs => rw [← b.sum_repr y]

  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.BilinForm.dualBasis_repr_apply, mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  rfl
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem isY_map {R R' : Type} [CommRing R] [CommRing R'] {n m : ℕ} (f : R →+* R') (p : GL (Fin n) R)
    (hp : IsY m p.val) : IsY m (GeneralLinearGroup.map f p).val := by
  intro i hi
  obtain ⟨h1, h2⟩ := hp i hi
  refine ⟨?_, fun j hj => ?_⟩
  · change f (p.val i i) = 1
    rw [h1, map_one]
  · change f (p.val i j) = 0
    rw [h2 j hj, map_zero]

private theorem chart_smul {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (f f' : GA E n → ℂ)
    (g g' : GA E n) (a : ℂ) (h : ∀ y, f (g * infGL E n y) = a * f' (g' * infGL E n y)) (x : Lie E n) :
    chart f g x = a * chart f' g' x := by
  unfold chart
  split_ifs with hx
  · exact h _
  · simp

theorem UpperTheory.V.Af.StrongMultiplicityOne.killP :
    UpperTheory.V.Af.StrongMultiplicityOne.ArchKir → UpperTheory.V.Af.StrongMultiplicityOne.FinKir → UpperTheory.V.Af.StrongMultiplicityOne.EmbY → UpperTheory.V.Af.StrongMultiplicityOne.PsiInf → UpperTheory.V.Af.StrongMultiplicityOne.ChartCont → UpperTheory.V.Af.StrongMultiplicityOne.KillP := by
  intro hA hF hE hP hC E _ _ _ n hn S U
  obtain ⟨c, Hf, hf1, hc, hf⟩ := hF E n hn S U
  obtain ⟨Hi, hi1, hi⟩ := hA E n (n - 1) (by omega)
  refine ⟨c, fun p => Hi (GeneralLinearGroup.map (pInf E) p) * Hf (GeneralLinearGroup.map (pFin E) p),
    by simp [hi1, hf1], hc, fun α => ?_⟩
  obtain ⟨β, hβ⟩ := hi α
  refine ⟨β, fun W hW hb hWh hU p hp => ?_⟩
  obtain ⟨C, hb⟩ := hb
  have hpi := isY_map (pInf E) p hp.1
  have hpf := isY_map (pFin E) p hp.1
  have hS := hp.2
  beta_reduce
  have e : p = finGL E n (GeneralLinearGroup.map (pFin E) p) * infGL E n (GeneralLinearGroup.map (pInf E) p) := by
    rw [← GlobalTheory.CuspRep.infGL_comm, GlobalTheory.CuspRep.infGL_mul_finGL]
  generalize GeneralLinearGroup.map (pInf E) p = a at *
  generalize GeneralLinearGroup.map (pFin E) p = b at *
  have h1 : ∀ x, chart (fop c W) (finGL E n b) x = Hf b * chart W 1 x := by
    refine chart_smul _ _ _ _ _ fun y => ?_
    have := hf (fun k => W (finGL E n k * infGL E n y)) (fun ν _ hν g _ => ?_) (fun g _ u hu _ => ?_) b hS hpf
    · simp only [map_one] at this
      rw [← this]
      unfold fop comb
      refine Finsupp.sum_congr fun x _ => ?_
      beta_reduce
      rw [map_mul, mul_assoc, mul_assoc, GlobalTheory.CuspRep.infGL_comm]
    · obtain ⟨k1, k2⟩ := (hE E n 0).2.1 ν hν
      rw [map_mul, mul_assoc, hWh _ k1, k2]
      rfl
    · rw [map_mul, mul_assoc, ← GlobalTheory.CuspRep.infGL_comm, ← mul_assoc, hU _ u hu]
  have h2 := hβ (chart W 1) ((hC E n W hW).2 1) ⟨max C 0, fun x => ?_⟩ (fun ν hν x => ?_) a hpi
  · unfold conv
    rw [e, GlobalTheory.CuspRep.chart_mul]
    simp only [Function.comp_apply, h1, mul_assoc]
    rw [integral_const_mul, h2]
    ring
  · unfold chart
    split_ifs
    · exact (hb _).trans (le_max_left _ _)
    · simp
  · obtain ⟨k1, k2⟩ := (hE E n 0).2.2.1 ν hν
    have := congrFun (GlobalTheory.CuspRep.chart_mul W 1 ν) x
    rw [Function.comp_apply] at this
    rw [← this]
    refine chart_smul _ _ _ _ _ (fun y => ?_) x
    rw [one_mul, one_mul, hWh _ k1, k2, hP]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem corner_isY {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (m : ℕ) (s : R →ₙ+* S) (y : GL (Fin n) R)
    (h : IsY m y.val) :
    IsY m (GlobalTheory.CuspRep.cornerGL n s y).val ∧ supN (GlobalTheory.CuspRep.cornerGL n s y).val = s (supN y.val) := by
  have e : ∀ i j, (GlobalTheory.CuspRep.cornerGL n s y).val i j =
      (1 : Matrix (Fin n) (Fin n) S) i j - s ((1 : Matrix (Fin n) (Fin n) R) i j) + s (y.val i j) := fun _ _ => rfl
  refine ⟨fun i hi => ⟨?_, fun j hj => ?_⟩, ?_⟩
  · rw [e, (h i hi).1]; simp
  · rw [e, (h i hi).2 j hj, Matrix.one_apply_ne hj.ne', Matrix.one_apply_ne hj.ne']; simp
  · unfold supN

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · have hne : i ≠ j := fun h' => by subst h'; omega
      rw [e, Matrix.one_apply_ne hne, Matrix.one_apply_ne hne]; simp
    · simp

theorem UpperTheory.V.Af.StrongMultiplicityOne.embY :
    UpperTheory.V.Af.StrongMultiplicityOne.EmbY := by
  intro E _ _ _ n m
  exact ⟨fun w y h => corner_isY m (sLoc E w) y h, fun y h => corner_isY m (sFin E) y h,
    fun y h => corner_isY m (sInf E) y h, fun w => GlobalTheory.CuspRep.CuspSub.continuous_locGL w⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

section

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem pr_comm {S : Finset (HeightOneSpectrum (𝓞 E))} {x k : GL (Fin n) (Af E)} (hx : SuppIn S x)
    (hk : Away S k) : k * x = x * k := by
  refine cmp_ext fun w => ?_
  rw [map_mul, map_mul]
  by_cases h : w ∈ S
  · rw [hk w h, mul_one, one_mul]
  · rw [hx w h, mul_one, one_mul]

private theorem pr_sLoc (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) : pLoc E w (sLoc E w x) = x := by
  classical
  exact Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w x

private theorem pr_sLoc_ne {v w : HeightOneSpectrum (𝓞 E)} (h : v ≠ w) (x : w.adicCompletion E) :
    pLoc E v (sLoc E w x) = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) h x

private theorem pr_loc {S : Finset (HeightOneSpectrum (𝓞 E))} {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ S)
    {k : GL (Fin n) (w.adicCompletion E)} (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) : InKS S (locGL E n w k) := by
  have h1 : ∀ v, v ≠ w → cmp v (locGL E n w k) = 1 := fun v hv =>
    GlobalTheory.CuspRep.map_cornerGL_of_zero _ _ (pr_sLoc_ne hv) k
  have h2 : cmp w (locGL E n w k) = k :=
    GlobalTheory.CuspRep.map_cornerGL_of_hom _ _ (RingHom.id _) (pr_sLoc w) k
  refine ⟨fun v hv => h1 v fun e => hw (e ▸ hv), fun v => ?_⟩
  by_cases h : v = w
  · subst h; rw [h2]; exact hk
  · rw [h1 v h]; exact one_mem _

private theorem pr_fop {S : Finset (HeightOneSpectrum (𝓞 E))} {c : GL (Fin n) (Af E) →₀ ℂ}
    (hc : ∀ x ∈ c.support, SuppIn S x) {f : GA E n → ℂ} (hf : ∀ g k, InKS S k → f (g * finGL E n k) = f g)
    (g : GA E n) (k : GL (Fin n) (Af E)) (hk : InKS S k) : fop c f (g * finGL E n k) = fop c f g := by
  unfold fop
  refine Finsupp.sum_congr fun x hx => ?_
  rw [mul_assoc, ← map_mul, pr_comm (hc x hx) hk.1, map_mul, ← mul_assoc, hf _ _ hk]

private theorem pr_wh {f : GA E n → ℂ} {u : GA E n} (hf : ∀ g, f (g * u) = f g) (g : GA E n) :
    whittaker f (g * u) = whittaker f g := by
  unfold whittaker
  simp only [← mul_assoc, hf]

private theorem pr_conv [_root_.NumberField.IsTotallyComplex E] {f : GA E n → ℂ} {k : GL (Fin n) (Af E)} (hf : ∀ g, f (g * finGL E n k) = f g)
    (α : Lie E n → ℂ) (g : GA E n) : conv f α (g * finGL E n k) = conv f α g := by
  unfold Af.StrongMultiplicityOne.conv
  congr 1
  funext x
  congr 1
  unfold chart
  split_ifs with h
  · rw [mul_assoc, ← GlobalTheory.CuspRep.infGL_comm, ← mul_assoc, hf]
  · rfl

private theorem pr_mem {U : Submodule ℂ (cuspForms E n)} (sU : Fb.Stab U) (c : GL (Fin n) (Af E) →₀ ℂ)
    {φ : cuspForms E n} (hφ : φ ∈ U) : ∃ ψ ∈ U, ψ.1 = fop c φ.1 := by
  refine ⟨∑ x ∈ c.support, c x • finRepCusp E n x φ, U.sum_mem fun x _ => U.smul_mem _ (sU.τ _ _ hφ), ?_⟩
  funext g
  rw [Submodule.coe_sum, Finset.sum_apply, fop, ← Fb.finEmb_eq]
  rfl

end

theorem UpperTheory.V.Af.StrongMultiplicityOne.pair :
    UpperTheory.V.Af.StrongMultiplicityOne.Seed → UpperTheory.V.Af.StrongMultiplicityOne.SetUp → UpperTheory.V.Af.StrongMultiplicityOne.KillP → UpperTheory.V.Af.StrongMultiplicityOne.Vanish → UpperTheory.V.Af.Smo.WhBasic → UpperTheory.V.Af.Smo.WhLin → UpperTheory.V.Af.StrongMultiplicityOne.ConvNice → UpperTheory.V.Af.StrongMultiplicityOne.NiceOf → UpperTheory.V.Af.StrongMultiplicityOne.EigMap → UpperTheory.V.Af.StrongMultiplicityOne.Pair := by
  intro hSeed hSet hKill hVan hWB hWL hCN hES hEM E _ _ _ n hn π π' h0 h0' hc hc' st st' hs
  have hN : ∀ φ ∈ π, Nice φ.1 := fun φ hφ => (hES E n φ).2 (hc hφ)
  have hN' : ∀ φ ∈ π', Nice φ.1 := fun φ hφ => (hES E n φ).2 (hc' hφ)
  obtain ⟨φ, hφ, α, hα⟩ := hSeed E n π h0 hc st
  obtain ⟨φ', hφ', α', hα'⟩ := hSeed E n π' h0' hc' st'
  obtain ⟨S, B, hS, hK, hK'⟩ := hSet E n π π' hs φ φ'
  obtain ⟨V, hV⟩ := (hN φ hφ).level
  obtain ⟨V', hV'⟩ := (hN' φ' hφ').level
  obtain ⟨c, H, hH, hc, hop⟩ := hKill E n hn S (V ⊓ V')

  have side : ∀ (σ : Submodule ℂ (cuspForms E n)), Fb.Stab σ → (∀ φ ∈ σ, Nice φ.1) → (∀ w ∉ S, Sat w (B w) σ) → ∀ φ ∈ σ,
      ∀ α : 𝓢(Lie E n, ℂ), conv (whittaker φ.1) α 1 = 1 → (∀ g k, InKS S k → φ.1 (g * finGL E n k) = φ.1 g) →
      (∀ g, ∀ u ∈ V ⊓ V', φ.1 (g * finGL E n u) = φ.1 g) →
      ∃ ψ ∈ σ, ∃ β : 𝓢(Lie E n, ℂ), Nice (conv ψ.1 β) ∧ (∀ w ∉ S, EigAt w (B w) (conv ψ.1 β)) ∧
        (∀ g k, InKS S k → conv ψ.1 β (g * finGL E n k) = conv ψ.1 β g) ∧
        ∀ p, InPS S p → whittaker (conv ψ.1 β) p = H p := by
    intro σ sσ hN hsat φ hφ α hα hK hU
    obtain ⟨ψ, hψ, e⟩ := pr_mem sσ c hφ
    obtain ⟨β, hβ⟩ := hop α
    have hK₁ : ∀ g k, InKS S k → ψ.1 (g * finGL E n k) = ψ.1 g := by
      rw [e]; exact pr_fop hc hK
    refine ⟨ψ, hψ, β, (hCN E n _ (hN ψ hψ) β).1, fun w hw => ?_, fun g k hk => pr_conv (fun g => hK₁ g k hk) _ g,
      fun p hp => ?_⟩
    · exact (hEM E n w (B w) _ (hsat w hw ψ hψ
        fun g k hk => hK₁ g _ (pr_loc hw hk))).2.1 (hN ψ hψ) β
    · obtain ⟨b1, b2, b3⟩ := hWB E n _ (hN φ hφ)
      rw [(hCN E n _ (hN ψ hψ) β).2, e, ((hWL E n _ (hN φ hφ)).1 c).2,
        hβ _ b1 b2 b3 (fun g u hu => pr_wh (fun g => hU g u hu) g) p hp, hα, mul_one]
  obtain ⟨ψ, hψ, β, n1, e1, k1, w1⟩ := side π st hN (fun w hw => (hS w hw).2.1) φ hφ α hα hK
    fun g u hu => hV g u hu.1
  obtain ⟨ψ', hψ', β', n2, e2, k2, w2⟩ := side π' st' hN' (fun w hw => (hS w hw).2.2) φ' hφ' α' hα' hK'
    fun g u hu => hV' g u hu.2
  obtain ⟨n3, w3⟩ := (hWL E n _ n1).2 _ n2
  refine ⟨ψ, hψ, ψ', hψ', β, β', sub_eq_zero.1 (hVan E n hn S B _ n3
    (fun w hw => ⟨(hS w hw).1, (hEM E n w (B w) _ (e1 w hw)).2.2 _ (e2 w hw)⟩) (fun g k hk => ?_) fun p hp => ?_),
    fun h00 => ?_⟩
  · rw [Pi.sub_apply, Pi.sub_apply, k1 g k hk, k2 g k hk]
  · rw [w3, Pi.sub_apply, w1 p hp, w2 p hp, sub_self]
  · have h1 : InPS S (1 : GA E n) := by
      refine ⟨fun i _ => ⟨by simp, fun j hj => ?_⟩, fun w _ => by rw [map_one, map_one]⟩
      exact Matrix.one_apply_ne hj.ne'
    have h2 := w1 1 h1
    rw [h00, hH] at h2
    simp [whittaker] at h2
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.normTwist :
    UpperTheory.V.Af.StrongMultiplicityOne.NormTwist := by
  intro E _ _ _ n hn π
  obtain ⟨κ, hκ⟩ := GlobalTheory.CuspRep.Central.exists_hasCentral E n π
  let z : {r : ℝ // 0 < r} →* (Ad E)ˣ :=
    (Reduction.posIdeleHom E).comp (Reduction.rpowHom ((n * Module.finrank ℚ E : ℝ))⁻¹)
  have hz : ∀ s, Reduction.centralSection E n s = GeneralLinearGroup.scalar (Fin n) (z s) := fun s => Units.ext rfl
  have hc : Continuous z := Reduction.continuous_posIdeleHom.comp (Reduction.continuous_rpowHom _)
  have hm : ∀ s, GroundTheory.Global.IdeleGroup.ideleModule E (z s ^ n) = s := fun s => by
    have h := Reduction.detModule_centralSection (K := E) hn s
    rw [hz] at h
    refine Eq.trans (congrArg _ (Units.ext ?_)) h
    change _ = Matrix.det (Matrix.diagonal fun _ : Fin n => (z s).val)
    simp
  let ν : Formalism.L2.Host.HChar E := ⟨(κ⁻¹.1.comp z).comp (GroundTheory.Global.IdeleGroup.ideleModule E),
    (κ⁻¹.2.1.comp hc).comp GroundTheory.Global.IdeleGroup.continuous_ideleModule, fun k => by
      have h := GroundTheory.Global.IdeleGroup.ideleModule_diagonal (K := E) k
      exact (congrArg (κ⁻¹.1.comp z) h).trans (map_one _)⟩
  refine ⟨ν, fun φ hφ s g => ?_⟩
  rw [hz, (hκ.twist ν).apply hφ]
  have e : (κ * ν ^ n).1 (z s) = 1 := by
    change κ.1 (z s) * (ν.1 ^ n) (z s) = 1
    rw [MonoidHom.pow_apply, ← map_pow]
    change κ.1 (z s) * (κ.1 (z (GroundTheory.Global.IdeleGroup.ideleModule E (z s ^ n))))⁻¹ = 1
    rw [hm, mul_inv_cancel]
  rw [e]
  simp
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.compl :
    UpperTheory.V.Af.StrongMultiplicityOne.Compl := by
  intro E _ _ n μ _ U l hs
  have hStable : Fb.Stab (orthRel (CuspidalSpectrum.cuspToL2 μ) (centralCuspForms E n) U) := by
    refine ⟨fun X φ hφ => ?_, fun k φ hφ => ?_, fun g φ hφ => ?_⟩
    · refine map_mem_orthRel (A' := fun y => -(gkModuleCusp E n).ρ X y) (Fb.stab_central.ρ X)
        (fun x hx y hy => ?_) (fun u hu => U.neg_mem (hs.ρ X u hu)) hφ
      rw [map_neg, inner_neg_left, neg_eq_iff_add_eq_zero]
      exact petersson_inner_lieAlgebra_skewAdjoint μ X (l hx) hy
    · refine map_mem_orthRel (A' := (gkModuleCusp E n).σ k⁻¹) (Fb.stab_central.σ k)
        (fun x hx y hy => ?_) (hs.σ k⁻¹) hφ
      have hInv : (gkModuleCusp E n).σ k ((gkModuleCusp E n).σ k⁻¹ x) = x := by
        change ((gkModuleCusp E n).σ k * (gkModuleCusp E n).σ k⁻¹) x = x
        simp only [← map_mul (gkModuleCusp E n).σ k k⁻¹, mul_inv_cancel, map_one,
          one_apply_eq_self]
      exact (petersson_inner_maximalCompact_invariant μ k (l (hs.σ k⁻¹ x hx)) hy).symm.trans
        (congrArg (fun z => inner ℂ (CuspidalSpectrum.cuspToL2 μ z)
          (CuspidalSpectrum.cuspToL2 μ ((gkModuleCusp E n).σ k y))) hInv)
    · refine map_mem_orthRel (A' := finRepCusp E n g⁻¹) (Fb.stab_central.τ g)
        (fun x hx y hy => ?_) (hs.τ g⁻¹) hφ
      have hInv : finRepCusp E n g (finRepCusp E n g⁻¹ x) = x := by
        change (finRepCusp E n g * finRepCusp E n g⁻¹) x = x
        simp only [← map_mul (finRepCusp E n) g g⁻¹, mul_inv_cancel, map_one,
          one_apply_eq_self]
      exact (petersson_inner_finiteAdelic_invariant μ g (l (hs.τ g⁻¹ x hx)) hy).symm.trans
        (congrArg (fun z => inner ℂ (CuspidalSpectrum.cuspToL2 μ z)
          (CuspidalSpectrum.cuspToL2 μ (finRepCusp E n g y))) hInv)
  exact ⟨orthRel (CuspidalSpectrum.cuspToL2 μ) (centralCuspForms E n) U,
    hStable, CuspidalSpectrum.sup_orthRel_centralCuspForms μ U l hs.ρ hs.τ,
    fun φ hφ φ' hφ' => hφ'.2 φ hφ⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.seed :
    UpperTheory.V.Af.Smo.WhBasic → UpperTheory.V.Af.StrongMultiplicityOne.SeedConv → UpperTheory.V.Af.StrongMultiplicityOne.NiceOf → UpperTheory.V.Af.StrongMultiplicityOne.Seed := by
  intro hW hS hN E _ _ _ n U hU l sU
  have nice : ∀ φ ∈ U, Nice φ.1 := fun φ hφ => (hN E n φ).2 (l hφ)
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hU
  have N := nice φ hφ
  have hg : ∃ g, whittaker φ.1 g ≠ 0 := by
    by_contra h
    refine h0 (Subtype.ext (MultiplicityOne.eq_zero_of_whittaker_eq_zero N.cont N.left N.cusp ?_
      fun g => not_not.1 fun h' => h ⟨g, h'⟩))
    rw [Fb.finEmb_eq]
    exact N.level
  obtain ⟨g, hg⟩ := hg
  rw [← GlobalTheory.CuspRep.infGL_mul_finGL g] at hg
  generalize GeneralLinearGroup.map (pInf E) g = y at hg
  generalize GeneralLinearGroup.map (pFin E) g = k at hg
  have hφ' := sU.τ k φ hφ
  refine ⟨_, hφ', hS E n _ (hW E n _ (nice _ hφ')).1 y ?_⟩
  have e : (finRepCusp E n k φ).1 = fun x => φ.1 (x * finGL E n k) := by
    rw [← Fb.finEmb_eq]
    rfl
  rw [e]
  simpa only [whittaker, mul_assoc] using hg
end
