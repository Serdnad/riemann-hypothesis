module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem isY_map {R R' : Type} [CommRing R] [CommRing R'] {n m : ℕ} (f : R →+* R') (p : GL (Fin n) R)
    (hp : IsY m p.val) : IsY m (GeneralLinearGroup.map f p).val := by
  intro i hi
  obtain ⟨h1, h2⟩ := hp i hi
  refine ⟨?_, fun j hj => ?_⟩
  · change f (p.val i i) = 1
    rw [h1, map_one]
  · change f (p.val i j) = 0
    rw [h2 j hj, map_zero]

private theorem chart_smul {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (f f' : GA E n → ℂ)
    (g g' : GA E n) (a : ℂ) (h : ∀ y, f (g * infGL E n y) = a * f' (g' * infGL E n y)) (x : Lie E n) :
    chart f g x = a * chart f' g' x := by
  unfold chart
  split_ifs with hx
  · exact h _
  · simp

theorem UpperTheory.V.Af.Smo.killP :
    UpperTheory.V.Af.Smo.ArchKir → UpperTheory.V.Af.Smo.FinKir → UpperTheory.V.Af.Smo.EmbY → UpperTheory.V.Af.Smo.PsiInf → UpperTheory.V.Af.Smo.ChartCont → UpperTheory.V.Af.Smo.KillP := by
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
    rw [← TR.infGL_comm, TR.infGL_mul_finGL]
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
      rw [map_mul, mul_assoc, mul_assoc, TR.infGL_comm]
    · obtain ⟨k1, k2⟩ := (hE E n 0).2.1 ν hν
      rw [map_mul, mul_assoc, hWh _ k1, k2]
      rfl
    · rw [map_mul, mul_assoc, ← TR.infGL_comm, ← mul_assoc, hU _ u hu]
  have h2 := hβ (chart W 1) ((hC E n W hW).2 1) ⟨max C 0, fun x => ?_⟩ (fun ν hν x => ?_) a hpi
  · unfold conv
    rw [e, TR.chart_mul]
    simp only [Function.comp_apply, h1, mul_assoc]
    rw [integral_const_mul, h2]
    ring
  · unfold chart
    split_ifs
    · exact (hb _).trans (le_max_left _ _)
    · simp
  · obtain ⟨k1, k2⟩ := (hE E n 0).2.2.1 ν hν
    have := congrFun (TR.chart_mul W 1 ν) x
    rw [Function.comp_apply] at this
    rw [← this]
    refine chart_smul _ _ _ _ _ (fun y => ?_) x
    rw [one_mul, one_mul, hWh _ k1, k2, hP]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

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

variable [IsTotallyReal E]

private theorem pr_conv {f : GA E n → ℂ} {k : GL (Fin n) (Af E)} (hf : ∀ g, f (g * finGL E n k) = f g)
    (α : Lie E n → ℂ) (g : GA E n) : conv f α (g * finGL E n k) = conv f α g := by
  unfold Af.Smo.conv
  congr 1
  funext x
  congr 1
  unfold chart
  split_ifs with h
  · rw [mul_assoc, ← TR.infGL_comm, ← mul_assoc, hf]
  · rfl

private theorem pr_mem (π : CuspSub E n) (c : GL (Fin n) (Af E) →₀ ℂ) {φ : TR.Sm E n} (hφ : φ ∈ π.V) :
    ∃ ψ ∈ π.V, ψ.1 = fop c φ.1 := by
  refine ⟨∑ x ∈ c.support, c x • TR.act (.fin x) φ,
    π.V.sum_mem fun x _ => π.V.smul_mem _ (π.stable _ _ hφ), ?_⟩
  funext g
  rw [Submodule.coe_sum, Finset.sum_apply]
  rfl

end

theorem UpperTheory.V.Af.Smo.pair :
    UpperTheory.V.Af.Smo.Seed → UpperTheory.V.Af.Smo.SetUp → UpperTheory.V.Af.Smo.KillP → UpperTheory.V.Af.Smo.Vanish → UpperTheory.V.Af.Smo.WhBasic → UpperTheory.V.Af.Smo.WhLin → UpperTheory.V.Af.Smo.ConvNice → UpperTheory.V.Af.Smo.EigOfSat → UpperTheory.V.Af.Smo.EigMap → UpperTheory.V.Af.Smo.Pair := by
  intro hSeed hSet hKill hVan hWB hWL hCN hES hEM E _ _ _ n hn π π' hc hc' hs
  obtain ⟨hN, φ, hφ, α, hα⟩ := hSeed E n π hc
  obtain ⟨hN', φ', hφ', α', hα'⟩ := hSeed E n π' hc'
  obtain ⟨S, B, hS, hK, hK'⟩ := hSet E n π π' hs φ hφ φ' hφ'
  obtain ⟨V, hV⟩ := (hN φ hφ).level
  obtain ⟨V', hV'⟩ := (hN' φ' hφ').level
  obtain ⟨c, H, hH, hc, hop⟩ := hKill E n hn S (V ⊓ V')

  have side : ∀ (σ : CuspSub E n), (∀ φ ∈ σ.V, Nice φ.1) → (∀ w ∉ S, σ.HasSat w (B w)) → ∀ φ ∈ σ.V,
      ∀ α : 𝓢(Lie E n, ℂ), conv (whittaker φ.1) α 1 = 1 → (∀ g k, InKS S k → φ.1 (g * finGL E n k) = φ.1 g) →
      (∀ g, ∀ u ∈ V ⊓ V', φ.1 (g * finGL E n u) = φ.1 g) →
      ∃ ψ ∈ σ.V, ∃ β : 𝓢(Lie E n, ℂ), Nice (conv ψ.1 β) ∧ (∀ w ∉ S, EigAt w (B w) (conv ψ.1 β)) ∧
        (∀ g k, InKS S k → conv ψ.1 β (g * finGL E n k) = conv ψ.1 β g) ∧
        ∀ p, InPS S p → whittaker (conv ψ.1 β) p = H p := by
    intro σ hN hsat φ hφ α hα hK hU
    obtain ⟨ψ, hψ, e⟩ := pr_mem σ c hφ
    obtain ⟨β, hβ⟩ := hop α
    have hK₁ : ∀ g k, InKS S k → ψ.1 (g * finGL E n k) = ψ.1 g := by
      rw [e]; exact pr_fop hc hK
    refine ⟨ψ, hψ, β, (hCN E n _ (hN ψ hψ) β).1, fun w hw => ?_, fun g k hk => pr_conv (fun g => hK₁ g k hk) _ g,
      fun p hp => ?_⟩
    · exact (hEM E n w (B w) _ (hES E n σ w (B w) (hsat w hw) ψ hψ
        fun g k hk => hK₁ g _ (pr_loc hw hk))).2.1 (hN ψ hψ) β
    · obtain ⟨b1, b2, b3⟩ := hWB E n _ (hN φ hφ)
      rw [(hCN E n _ (hN ψ hψ) β).2, e, ((hWL E n _ (hN φ hφ)).1 c).2,
        hβ _ b1 b2 b3 (fun g u hu => pr_wh (fun g => hU g u hu) g) p hp, hα, mul_one]
  obtain ⟨ψ, hψ, β, n1, e1, k1, w1⟩ := side π hN (fun w hw => (hS w hw).2.1) φ hφ α hα hK
    fun g u hu => hV g u hu.1
  obtain ⟨ψ', hψ', β', n2, e2, k2, w2⟩ := side π' hN' (fun w hw => (hS w hw).2.2) φ' hφ' α' hα' hK'
    fun g u hu => hV' g u hu.2
  obtain ⟨n3, w3⟩ := (hWL E n _ n1).2 _ n2
  refine ⟨ψ, hψ, ψ', hψ', β, β', sub_eq_zero.1 (hVan E n hn S B _ n3
    (fun w hw => ⟨(hS w hw).1, (hEM E n w (B w) _ (e1 w hw)).2.2 _ (e2 w hw)⟩) (fun g k hk => ?_) fun p hp => ?_),
    fun h0 => ?_⟩
  · rw [Pi.sub_apply, Pi.sub_apply, k1 g k hk, k2 g k hk]
  · rw [w3, Pi.sub_apply, w1 p hp, w2 p hp, sub_self]
  · have h1 : InPS S (1 : GA E n) := by
      refine ⟨fun i _ => ⟨by simp, fun j hj => ?_⟩, fun w _ => by rw [map_one, map_one]⟩
      exact Matrix.one_apply_ne hj.ne'
    have h2 := w1 1 h1
    rw [h0, hH] at h2
    simp [whittaker] at h2
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem fin_bad {E : Type} [Field E] [NumberField E] {n : ℕ} (k : GL (Fin n) (Af E)) :
    {w | cmp w k ∉ GlobalTheory.LFun.KGL w (n := n)}.Finite := by
  have h : ∀ x : Af E, ∀ᶠ w in Filter.cofinite, pLoc E w x ∈ Formalism.UG.Ov E w := fun x => x.2
  have h1 : ∀ᶠ w in Filter.cofinite, ∀ i j, pLoc E w (k.val i j) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  have h2 : ∀ᶠ w in Filter.cofinite, ∀ i j, pLoc E w ((k⁻¹).val i j) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  have h3 : ∀ᶠ w in Filter.cofinite, cmp w k ∈ GlobalTheory.LFun.KGL w (n := n) := by
    filter_upwards [h1, h2] with w a b
    rw [GlobalTheory.AdelicU.mem_GLint_iff, ← map_inv]
    exact ⟨a, b⟩
  exact h3

theorem UpperTheory.V.Af.Smo.awayInd :
    UpperTheory.V.Af.Smo.AwayInd := by
  intro E _ _ n S P h0 h1
  classical
  suffices H : ∀ T : Finset (HeightOneSpectrum (𝓞 E)), ∀ k, Away S k → (∀ w ∉ T, cmp w k ∈ GlobalTheory.LFun.KGL w (n := n)) → P k by
    intro k hk
    refine H (fin_bad k).toFinset k hk fun w hw => ?_
    by_contra h
    exact hw ((Set.Finite.mem_toFinset _).2 h)
  intro T
  induction T using Finset.induction_on with
  | empty => exact fun k hk h => h0 k ⟨hk, fun w => h w (Finset.notMem_empty w)⟩
  | insert w T hw ih =>
    intro k hk h
    by_cases hS : w ∈ S
    · refine ih k hk fun v hv => ?_
      by_cases e : v = w
      · subst e; rw [hk v hS]; exact one_mem _
      · exact h v (by simp [e, hv])
    · have e1 : cmp w (k * (locGL E n w (cmp w k))⁻¹) = 1 := by
        rw [map_mul, map_inv, GlobalTheory.CuspRep.pLoc_locGL, mul_inv_cancel]
      have e2 : ∀ v, v ≠ w → cmp v (k * (locGL E n w (cmp w k))⁻¹) = cmp v k := fun v e => by
        rw [map_mul, map_inv, GlobalTheory.CuspRep.pLoc_locGL_of_ne e, inv_one, mul_one]
      have a : Away S (k * (locGL E n w (cmp w k))⁻¹) := fun v hv => by
        rw [e2 v (fun e => hS (e ▸ hv)), hk v hv]
      have p := ih _ a fun v hv => by
        by_cases e : v = w
        · subst e; rw [e1]; exact one_mem _
        · rw [e2 v e]; exact h v (by simp [e, hv])
      have q := h1 w hS _ a e1 p (cmp w k)
      rwa [inv_mul_cancel_right] at q
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private def sc {R : Type} [CommRing R] (n : ℕ) : GL (Fin 1) R →* GL (Fin n) R :=
  (GeneralLinearGroup.scalar (Fin n)).comp GeneralLinearGroup.det

private theorem sc_val {R : Type} [CommRing R] (n : ℕ) (x : GL (Fin 1) R) (i j : Fin n) :
    (sc n x).val i j = if i = j then x.val 0 0 else 0 := by
  change Matrix.scalar (Fin n) (Matrix.det x.val) i j = _
  rw [Matrix.det_fin_one]
  by_cases e : i = j <;> simp [e]

private theorem sc_scalar {R : Type} [CommRing R] (n : ℕ) (z : Rˣ) :
    sc n (GeneralLinearGroup.scalar (Fin 1) z) = GeneralLinearGroup.scalar (Fin n) z := by
  ext i j
  rw [sc_val]
  change (if i = j then Matrix.scalar (Fin 1) z.val 0 0 else 0) = Matrix.scalar (Fin n) z.val i j
  by_cases e : i = j <;> simp [e]

private theorem sc_comm {R : Type} [CommRing R] (n : ℕ) (x : GL (Fin 1) R) (g : GL (Fin n) R) :
    sc n x * g = g * sc n x :=
  Units.ext (Matrix.scalar_commute (Matrix.det x.val) (fun _ => Commute.all _ _) g.val).eq

private theorem map_sc {R S : Type} [CommRing R] [CommRing S] (n : ℕ) (p : R →+* S) (x : GL (Fin 1) R) :
    GeneralLinearGroup.map p (sc n x) = sc n (GeneralLinearGroup.map p x) := by
  ext i j
  change p ((sc n x).val i j) = _
  rw [sc_val, sc_val]
  split_ifs
  · rfl
  · exact map_zero p

private theorem corner_sc {R S : Type} [CommRing R] [CommRing S] (n : ℕ) (s : R →ₙ+* S) (x : GL (Fin 1) R) :
    GlobalTheory.CuspRep.cornerGL n s (sc n x) = sc n (GlobalTheory.CuspRep.cornerGL 1 s x) := by
  ext i j
  rw [sc_val]
  change (1 : Matrix (Fin n) (Fin n) S) i j - s ((1 : Matrix (Fin n) (Fin n) R) i j) + s ((sc n x).val i j) =
    if i = j then (1 : Matrix (Fin 1) (Fin 1) S) 0 0 - s ((1 : Matrix (Fin 1) (Fin 1) R) 0 0) + s (x.val 0 0) else 0
  rw [sc_val]
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

private theorem continuous_sc {R : Type} [CommRing R] [TopologicalSpace R] (n : ℕ) :
    Continuous (sc n : GL (Fin 1) R → GL (Fin n) R) := by
  have h : Continuous fun x : GL (Fin 1) R => (sc n x).val := by
    refine continuous_matrix fun i j => ?_
    simp only [sc_val]
    split_ifs
    · exact Units.continuous_val.matrix_elem 0 0
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  refine continuous_matrix fun i j => ?_
  simp only [sc_val]
  split_ifs
  · exact Units.continuous_coe_inv.matrix_elem 0 0
  · exact continuous_const

private theorem sc_mem {K : Type} [Field K] (n : ℕ) (O : Subring K) (x : GL (Fin 1) K)
    (h : x ∈ Formalism.UG.GLint (Fin 1) O) : sc n x ∈ Formalism.UG.GLint (Fin n) O := by
  rw [GlobalTheory.AdelicU.mem_GLint_iff] at h ⊢
  rw [← map_inv]
  constructor <;> intro i j <;> rw [sc_val] <;> split_ifs
  · exact h.1 0 0
  · exact zero_mem _
  · exact h.2 0 0
  · exact zero_mem _

theorem UpperTheory.V.Af.Smo.centEq :
    UpperTheory.V.Af.Smo.CentLoc → UpperTheory.V.Af.Smo.AwayInd → UpperTheory.V.Af.Smo.DenseAway → UpperTheory.V.Af.Smo.CentEq := by
  intro hL hA hD E _ _ n S B f f' hc hc' hl hl' hE hK hK' z g g'
  have h1 : ∀ k : GL (Fin 1) (Af E), Away S k → ∀ g g' : GA E n,
      f (g * finGL E n (sc n k)) * f' g' = f g * f' (g' * finGL E n (sc n k)) := by
    refine hA E 1 S _ (fun k hk g g' => ?_) (fun w hw k _ _ hP y g g' => ?_)
    · have hk' : InKS S (sc n k) := by
        refine ⟨fun w hw => ?_, fun w => ?_⟩
        · rw [map_sc, hk.1 w hw, map_one]
        · rw [map_sc]; exact sc_mem n _ _ (hk.2 w)
      rw [hK g _ hk', hK' g' _ hk']
    · obtain ⟨c, hcc⟩ := hL E n w (B w) (GeneralLinearGroup.det y)
      have e : sc n (locGL E 1 w y) = locGL E n w (1 * GeneralLinearGroup.scalar (Fin n) (GeneralLinearGroup.det y)) := by
        rw [one_mul]; exact (corner_sc n (sLoc E w) y).symm
      have a := hcc _ ((hE w hw).1 (g * finGL E n (sc n k))) 1
      have b := hcc _ ((hE w hw).2 (g' * finGL E n (sc n k))) 1
      simp only [map_one, mul_one] at a b
      rw [map_mul, map_mul, ← mul_assoc, ← mul_assoc, e, a, b, mul_assoc, hP]
      ring
  have h2 : ∀ x : GA E 1, f (g * sc n x) * f' g' = f g * f' (g' * sc n x) := by
    refine isClosed_property (hD E 1 S).denseRange_val (isClosed_eq ?_ ?_) ?_
    · exact (hc.comp (continuous_const.mul (continuous_sc n))).mul continuous_const
    · exact continuous_const.mul (hc'.comp (continuous_const.mul (continuous_sc n)))
    · rintro ⟨_, γ, k, hk, rfl⟩
      have e : ∀ u : GA E n, u * sc n (ratGL E 1 γ * finGL E 1 k) = ratGL E n (sc n γ) * (u * finGL E n (sc n k)) := by
        intro u
        rw [map_mul, ← mul_assoc, ← sc_comm n (ratGL E 1 γ) u, mul_assoc]
        congr 1
        · exact (map_sc n _ γ).symm
        · exact congrArg _ (corner_sc n (sFin E) k).symm
      change f (g * sc n (ratGL E 1 γ * finGL E 1 k)) * _ = _ * f' (g' * sc n (ratGL E 1 γ * finGL E 1 k))
      rw [e, e]
      have a : ∀ u, f (ratGL E n (sc n γ) * u) = f u := hl _
      have b : ∀ u, f' (ratGL E n (sc n γ) * u) = f' u := hl' _
      rw [a, b]
      exact h1 k hk g g'
  rw [← sc_scalar]
  exact h2 _
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem scalar_comm' {K : Type} [Field K] {n : ℕ} (y : Kˣ) (g : GL (Fin n) K) :
    GeneralLinearGroup.scalar (Fin n) y * g = g * GeneralLinearGroup.scalar (Fin n) y :=
  Units.ext (Matrix.scalar_commute (y : K) (fun _ => Commute.all _ _) g.val).eq

private theorem finsum_top {K : Type} [Field K] {n : ℕ} (O : Subring K) (ϖ : Kˣ) (W : GL (Fin n) K → ℂ)
    (hW : ∀ g, ∀ k ∈ Formalism.UG.GLint (Fin n) O, W (g * k) = W g) (g : GL (Fin n) K) :
    ∑ᶠ c : GL (Fin n) K ⧸ Formalism.UG.GLint (Fin n) O, Formalism.UG.Tj ℂ n O (ϖ : K) n c.out * W (g * c.out) =
      W (g * GeneralLinearGroup.scalar (Fin n) ϖ) := by
  set z : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) ϖ with hz
  have hd : Formalism.UG.diagJ n (ϖ : K) n = z.val := by
    simp [Formalism.UG.diagJ, hz]
  rw [finsum_eq_single _ (z : GL (Fin n) K ⧸ Formalism.UG.GLint (Fin n) O)]
  · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (Formalism.UG.GLint (Fin n) O) z
    rw [hk, ← mul_assoc, hW _ _ k.2, Formalism.UG.Tj, Set.indicator_of_mem, Pi.one_apply, one_mul]
    exact ⟨1, one_mem _, k, k.2, by simp [hd]⟩
  · intro c hc
    rw [Formalism.UG.Tj, Set.indicator_of_notMem, zero_mul]
    rintro ⟨a, ha, b, hb, e⟩
    refine hc ?_
    have e' : c.out = z * (a * b) := by
      rw [← mul_assoc, hz, scalar_comm', ← hz]
      exact Units.ext (by rw [e, hd]; rfl)
    rw [← QuotientGroup.out_eq' c, e']
    exact QuotientGroup.mk_mul_of_mem _ (mul_mem ha hb)

private theorem scalar_mem {K : Type} [Field K] {n : ℕ} (O : Subring K) (u : Kˣ) (h : (u : K) ∈ O)
    (h' : ((u⁻¹ : Kˣ) : K) ∈ O) : GeneralLinearGroup.scalar (Fin n) u ∈ Formalism.UG.GLint (Fin n) O := by
  have key : ∀ x : Kˣ, (x : K) ∈ O → ∀ i j, (GeneralLinearGroup.scalar (Fin n) x).val i j ∈ O := fun x hx i j => by
    change Matrix.diagonal (fun _ => (x : K)) i j ∈ O
    rw [Matrix.diagonal_apply]
    split_ifs
    · exact hx
    · exact zero_mem _
  refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨key u h, ?_⟩
  rw [← map_inv]
  exact key _ h'

theorem UpperTheory.V.Af.Smo.centLoc :
    UpperTheory.V.Af.Smo.CentLoc := by
  intro E _ _ n w B y
  by_cases hB : B.card = n
  swap
  · exact ⟨0, fun W hW => absurd hW.card hB⟩
  let H : Subgroup (w.adicCompletion E)ˣ :=
    { carrier := {y | ∃ c : ℂ, c ≠ 0 ∧ ∀ W : GL (Fin n) (w.adicCompletion E) → ℂ, Eig w B W →
        ∀ g, W (g * GeneralLinearGroup.scalar (Fin n) y) = c * W g}
      one_mem' := ⟨1, one_ne_zero, fun W _ g => by simp⟩
      mul_mem' := by
        rintro a b ⟨c, hc, h⟩ ⟨d, hd, h'⟩
        exact ⟨d * c, mul_ne_zero hd hc, fun W hW g => by rw [map_mul, ← mul_assoc, h' W hW, h W hW, mul_assoc]⟩
      inv_mem' := by
        rintro a ⟨c, hc, h⟩
        refine ⟨c⁻¹, inv_ne_zero hc, fun W hW g => ?_⟩
        have := h W hW (g * GeneralLinearGroup.scalar (Fin n) a⁻¹)
        rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] at this
        rw [this, inv_mul_cancel_left₀ hc] }
  suffices hy : y ∈ H from hy.imp fun _ h => h.2
  obtain ⟨p, hp⟩ : ∃ p, Formalism.UG.IsUnifV E w p := w.valuedAdicCompletion_surjective E _
  have hp0 : p ≠ 0 := fun h0 => by simp [Formalism.UG.IsUnifV, h0] at hp
  have hne : GlobalTheory.LFun.satEig (Formalism.UG.qV E w) n B n ≠ 0 := by
    have hq := Multiset.powersetCard_self (B.map fun b : ℂˣ => (b : ℂ))
    rw [Multiset.card_map, hB] at hq
    simp [GlobalTheory.LFun.satEig, Multiset.esymm, hq]
  have hpH : Units.mk0 p hp0 ∈ H := ⟨_, hne, fun W hW g =>
    (finsum_top (Formalism.UG.Ov E w) (Units.mk0 p hp0) W hW.inv g).symm.trans (hW.eig p hp n le_rfl g)⟩
  have hu : ∀ u : (w.adicCompletion E)ˣ, Valued.v (u : w.adicCompletion E) = 1 → u ∈ H := fun u h =>
    ⟨1, one_ne_zero, fun W hW g => by
      rw [one_mul]
      refine hW.inv g _ (scalar_mem (Formalism.UG.Ov E w) u h.le ?_)
      change Valued.v ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1
      rw [Units.val_inv_eq_inv_val, map_inv₀, h, inv_one]⟩
  have hy0 : Valued.v (y : w.adicCompletion E) ≠ 0 := by simp
  have := hu (y * Units.mk0 p hp0 ^ WithZero.log (Valued.v (y : w.adicCompletion E))) (by
    have hp' : Valued.v p = WithZero.exp (-1 : ℤ) := hp
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_mk0, hp', ← WithZero.exp_zsmul]
    simp only [zsmul_neg, zsmul_one, Int.cast_id]
    rw [WithZero.exp_neg, WithZero.exp_log hy0, mul_inv_cancel₀ hy0])
  exact (H.mul_mem_cancel_right (H.zpow_mem hpH _)).1 this
end
