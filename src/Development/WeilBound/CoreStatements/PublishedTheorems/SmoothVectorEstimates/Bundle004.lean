module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace CharacterNondegenerate

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def chi (ψ : AddChar (Ad E) ℂ) : AddChar (Cinf E) ℂ := ψ.compAddMonoidHom (sInf E).toAddMonoidHom

theorem chi_apply (ψ : AddChar (Ad E) ℂ) (z : Cinf E) : chi ψ z = ψ (sInf E z) := rfl

theorem pInf_sInf (z : Cinf E) : pInf E (sInf E z) = z := (infEq E).symm_apply_apply z

theorem pFin_sInf (z : Cinf E) : pFin E (sInf E z) = 0 := rfl

theorem sInf_mul (z : Cinf E) (x : Ad E) : sInf E z * x = sInf E (z * pInf E x) := by
  refine ad_ext ?_ ?_
  · rw [map_mul, pInf_sInf, pInf_sInf]
  · rw [map_mul, pFin_sInf, pFin_sInf, zero_mul]

theorem continuous_sInf : Continuous (sInf E) :=
  ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))

omit [_root_.NumberField.IsTotallyComplex E] in
theorem nonempty_pl : Nonempty (Pl E) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩⟩

theorem continuous_chi {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) : Continuous (chi ψ) :=
  hψ.cont.comp continuous_sInf

theorem chi_nondeg {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (z : Cinf E) (hz : ∀ w, chi ψ (z * w) = 1) : z = 0 := by
  obtain ⟨d, hd⟩ := hψ.ann (sInf E z) fun c => by rw [sInf_mul]; exact hz _
  have hd0 : d = 0 := by
    by_contra h0
    obtain ⟨w⟩ := nonempty_pl (E := E)
    have h1 : sInf E z * algebraMap E (Ad E) d⁻¹ = 1 := by
      rw [hd, ← map_mul, mul_inv_cancel₀ h0, map_one]
    have h2 := congrArg (fun x => pLoc E w (pFin E x)) h1
    simp only [map_mul, pFin_sInf, zero_mul, map_zero, map_one] at h2
    exact zero_ne_one h2
  rw [← pInf_sInf z, hd, hd0, map_zero, map_zero]

theorem sInf_lastE (k : ℕ) (y : UnipotentBlockColumnIndex a k k → Cinf E) :
    sInf E (lastE k y) = lastE k (fun t => sInf E (y t)) := by

  simp only [lastE, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

theorem polyBd : PolyBd (repI E a) := ⟨1, 0, zero_le_one, fun g x => by
  show ‖Rt E a (infGL E a g) x‖ ≤ 1 * _ ^ 0 * ‖x‖
  rw [pow_zero, mul_one, one_mul, norm_Rt]⟩

end CharacterNondegenerate

open CharacterNondegenerate in
theorem whittaker_nondegenerate_character : S7 → MirabolicColumnBlock → G0 → G5 → G6 := by
  intro hS7 hS10 hG0 hG5 E _ _ _ a ψ hψ S Y Y' hY hY' n m hn hSt
  obtain ⟨φ, hφY, φ', hφY', hsm, hsm', hlev, hlev', hW1, hWeq⟩ := hSt
  obtain ⟨hcI, hcLI, hcIf, -, -, -, hcomm, -, hb, -⟩ := hG0 E a
  obtain ⟨hΛ, hRt, hGood, hlaw⟩ := hG5 E a ψ hψ
  obtain ⟨hdec, -, -, hBlk1, -⟩ := hS10 (Cinf E) a (n + 1)
  obtain ⟨η, r, hη1, hr1, hmir, -, -, hv⟩ := hS7 (InfinitePlace E) a (XB E a) (repI E a) polyBd n hn (chi ψ)
    (continuous_chi hψ) (fun z => hψ.norm _) (chi_nondeg hψ) Set.univ Filter.univ_mem
  have memY : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ g, ∀ x ∈ Z, repI E a g x ∈ Z :=
    fun Z hZ g x hx => hZ.stable _ (fun w _ => hcLI w g) x hx
  have whB : ∀ x : XB E a, Good ψ (a - 1) x → ∀ (y : UnipotentBlockColumnIndex a (n + 1) (n + 1) → Cinf E) (g : GA E a),
      Wh ψ x (infGL E a (blkU y) * g) = chi ψ (lastE (n + 1) y) * Wh ψ x g := by
    intro x hx y g
    rw [hb, chi_apply, sInf_lastE]
    exact (hlaw x hx).2.2 (n + 1) n.succ_pos _ g
  have lawOf : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ g' : GA E a, cInf g' = 1 →
      ∀ Λ : XB E a →L[ℂ] ℂ, (∀ x : XB E a, Good ψ (a - 1) x → Λ x = Wh ψ x g') →
      ∀ x ∈ Z, ∀ y : UnipotentBlockColumnIndex a (n + 1) (n + 1) → Cinf E,
        Λ (repI E a (blkU y) x) = chi ψ (lastE (n + 1) y) * Λ x := by
    intro Z hZ g' hg' Λ hΛg x hx y
    have hx' := hZ.good x hx
    change Λ (Rt E a (infGL E a (blkU y)) x) = _
    rw [hΛg _ (hGood x _ hx'), hΛg x hx', hRt, hcomm g' hg', whB x hx']
  have levOf : ∀ x x' : XB E a, Lev S x → (∀ Z : Submodule ℂ (XB E a), IsClosed (Z : Set (XB E a)) →
      (∀ g, ∀ y ∈ Z, repI E a g y ∈ Z) → x ∈ Z → x' ∈ Z) → Lev S x' := by
    intro x x' hx hZ w hw
    refine Filter.mem_of_superset (hx w hw) fun u hu => ?_
    have hu' : Rt E a (fl a w u) x = x := hu
    let T : XB E a →L[ℂ] XB E a := Rt E a (fl a w u) - ContinuousLinearMap.id ℂ _
    have hmem : ∀ y, T y = 0 ↔ Rt E a (fl a w u) y = y := fun y => by simp [T, sub_eq_zero]
    have hk := hZ _ T.isClosed_ker (fun g y hy => by
        rw [LinearMap.mem_ker] at hy ⊢
        refine (hmem _).2 ?_
        have hy' := (hmem y).1 hy
        change Rt E a (fl a w u) (Rt E a (infGL E a g) y) = Rt E a (infGL E a g) y
        rw [← ContinuousLinearMap.mul_apply, ← map_mul, hcomm _ (hcIf w u), map_mul,
          ContinuousLinearMap.mul_apply, hy'])
      (LinearMap.mem_ker.2 ((hmem x).2 hu'))
    rw [LinearMap.mem_ker] at hk
    exact (hmem x').1 hk
  obtain ⟨v, hvs, hvP⟩ := hv φ hsm
  obtain ⟨v', hvs', hvP'⟩ := hv φ' hsm'
  obtain ⟨hvY, hvΛ⟩ := hvP Y hY.closed (memY Y hY) hφY
  obtain ⟨hvY', hvΛ'⟩ := hvP' Y' hY'.closed (memY Y' hY') hφY'
  have conv : ∀ (g' : GA E a) (Λ : XB E a →L[ℂ] ℂ), (∀ x : XB E a, Good ψ (a - 1) x → Λ x = Wh ψ x g') →
      ∀ x : XB E a, Good ψ (a - 1) x → ∀ k, Λ (repI E a k x) = Wh ψ x (g' * infGL E a k) := by
    intro g' Λ hΛg x hx k
    change Λ (Rt E a (infGL E a k) x) = _
    rw [hΛg _ (hGood x _ hx), hRt]
  have hgY := hY.good
  have hgY' := hY'.good
  refine ⟨v, hvY, v', hvY', hvs, hvs', levOf φ v hlev fun Z hc hs hx => (hvP Z hc hs hx).1,
    levOf φ' v' hlev' fun Z hc hs hx => (hvP' Z hc hs hx).1, ?_, ?_⟩
  · obtain ⟨Λ₁, hΛ₁⟩ := hΛ 1
    have e1 := hvΛ Λ₁ (lawOf Y hY 1 (map_one _) Λ₁ hΛ₁) 1 hBlk1
    rw [conv 1 Λ₁ hΛ₁ v (hgY v hvY), conv 1 Λ₁ hΛ₁ φ (hgY φ hφY), hr1, map_one, one_mul] at e1
    rw [e1]
    exact mul_ne_zero hη1 hW1
  · intro g hg
    obtain ⟨hgI, hgL⟩ := hg
    obtain ⟨y, h, hh, hyh⟩ := hdec (cInf g) hgI
    obtain ⟨g', hg'⟩ : ∃ g' : GA E a, g' = (infGL E a (cInf g))⁻¹ * g := ⟨_, rfl⟩
    have hg'1 : cInf g' = 1 := by rw [hg', map_mul, map_inv, hcI, inv_mul_cancel]
    have hgeq : g = infGL E a (blkU y) * (g' * infGL E a h) := by
      rw [hcomm g' hg'1 h, ← mul_assoc, ← map_mul, ← hyh, hg', mul_inv_cancel_left]
    obtain ⟨Λ, hΛg⟩ := hΛ g'
    have e := hvΛ Λ (lawOf Y hY g' hg'1 Λ hΛg) h hh
    have e' := hvΛ' Λ (lawOf Y' hY' g' hg'1 Λ hΛg) h hh
    rw [conv g' Λ hΛg v (hgY v hvY), conv g' Λ hΛg φ (hgY φ hφY)] at e
    rw [conv g' Λ hΛg v' (hgY' v' hvY'), conv g' Λ hΛg φ' (hgY' φ' hφY')] at e'
    rw [hgeq, whB v (hgY v hvY), whB v' (hgY' v' hvY'), e, e']
    by_cases hη : η h = 0
    · simp [hη]
    · rw [hWeq _ ⟨?_, fun w => ?_⟩]
      · rw [map_mul, hg'1, one_mul, hcI]
        exact hmir h hh hη
      · rw [map_mul, hcLI, mul_one, hg', map_mul, map_inv, hcLI, inv_one, one_mul]
        exact hgL w

end PositivityTheory.jumpWindows

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace MirrorMap

theorem mir_map {R S : Type} [CommRing R] [CommRing S] {a m : ℕ} (p : R →+* S) {γ : GL (Fin a) R}
    (h : Mir m γ) : Mir m (GeneralLinearGroup.map p γ) := by
  intro i k hik
  change p (γ.val i k) = _
  rw [h i k hik, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem mirS_mul (h10 : MirabolicColumnBlock) {S : Finset (Pl E)} {x g : GA E a} (hx : Mir (a - 1) x) (hg : MirS S g) :
    MirS S (x * g) := by
  refine ⟨?_, fun w hw => ?_⟩
  · rw [map_mul]
    exact (h10 _ a (a - 1)).2.2.2.2.1 _ _ (mir_map (pInf E) hx) hg.1
  · rw [map_mul]
    exact (h10 _ a (a - 1)).2.2.2.2.1 _ _ (mir_map ((pLoc E w).comp (pFin E)) hx) (hg.2 w hw)

end MirrorMap

theorem mirror_global_of : MirabolicColumnBlock → G0 → G5 → G9 → PlacewiseToOutsideS → FourierUniquenessMirabolic → WeakApproximationGL → WhittakerVanishingImpliesZero := by
  intro h10 h0 h5 h9 h9b h11 h12 E _ _ _ a ψ hψ S hcond φ hgood hleft hsat hvan
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hproj, -⟩ := h0 E a
  have hcont : Continuous (Wh ψ φ) := ((h5 E a ψ hψ).2.2.2 φ hgood).1
  have step1 : ∀ g, MirS S g → Wh ψ φ g = 0 := by
    intro g hg
    obtain ⟨g₀, e1, e2, e3⟩ := hproj S g
    refine h9b E a S (Wh ψ φ) hcont ?_ g g₀ e1 e2 e3 ?_
    · intro w hw h hh hz u
      obtain ⟨B, hB⟩ := hsat w hw
      exact h9 E a ψ hψ w (hcond w hw) B φ hgood hB h hh hz u
    · refine hvan g₀ ⟨?_, fun w hw => ?_⟩ e3
      · rw [e1]; exact hg.1
      · rw [e2 w hw]; exact hg.2 w hw
  have step2 : ∀ g, MirS S g → φ g = 0 := by
    intro g hg
    refine h11 E a ψ hψ (a - 1) φ (by omega) hgood {g | MirS S g} ?_ ?_ step1 g hg
    · intro γ hγ g hg
      exact MirrorMap.mirS_mul h10 (MirrorMap.mir_map (algebraMap E (Ad E)) hγ) hg
    · intro k hk y g hg
      exact MirrorMap.mirS_mul h10 ((h10 (Ad E) a (a - 1)).2.2.2.2.2.1 k y hk) hg
  have hEq : (⇑φ) = fun _ => (0 : ℂ) := by
    refine Continuous.ext_on (h12 E a S) φ.continuous continuous_const ?_
    rintro x ⟨γ, g, rfl, hg1, hg2⟩
    show φ (ratGL E a γ * g) = 0
    rw [hleft]
    refine step2 g ⟨?_, fun w hw => ?_⟩
    · rw [hg1]; exact (h10 _ a (a - 1)).2.2.1
    · rw [hg2 w hw]; exact (h10 _ a (a - 1)).2.2.1
  ext x
  simpa using congrFun hEq x

end PositivityTheory.jumpWindows

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace GeneralLinearEntryConvergence

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem tendsto_af {ι : Type} {l : Filter ι} (x : Af E) (z : ι → Af E)
    (h1 : ∀ w : Pl E, ∀ᶠ t in l, z t w = x w)
    (h2 : ∀ᶠ t in l, ∀ w : Pl E, z t w - x w ∈ w.adicCompletionIntegers E) :
    Tendsto z l (𝓝 x) := by
  classical
  let A : ∀ w : Pl E, Set (w.adicCompletion E) := fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))
  let sm : (∀ w : Pl E, A w) → Af E := fun y =>
    RestrictedProduct.structureMap (fun w : Pl E => w.adicCompletion E) A cofinite y
  have hsm : Continuous sm :=
    (RestrictedProduct.isEmbedding_structureMap (R := fun w : Pl E => w.adicCompletion E) (A := A)
      (𝓕 := cofinite)).continuous
  let u0 : ∀ w : Pl E, A w := fun w => ⟨0, zero_mem (w.adicCompletionIntegers E)⟩
  let u : ι → ∀ w : Pl E, A w := fun t w =>
    if h : z t w - x w ∈ w.adicCompletionIntegers E then ⟨_, h⟩ else u0 w
  have hu : Tendsto u l (𝓝 u0) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h1 w] with t ht
    have h0 : z t w - x w ∈ w.adicCompletionIntegers E := by
      rw [ht, sub_self]; exact zero_mem _
    simp only [u, dif_pos h0]
    apply Subtype.ext
    change (0 : w.adicCompletion E) = z t w - x w
    rw [ht, sub_self]
  have hv : Tendsto (fun t => sm (u t)) l (𝓝 (sm u0)) := (hsm.tendsto u0).comp hu
  have e0 : sm u0 = 0 := by
    ext w
    rfl
  rw [e0] at hv
  have hv' : Tendsto (fun t => z t - x) l (𝓝 0) := by
    refine hv.congr' ?_
    filter_upwards [h2] with t ht
    apply Subtype.ext
    funext w
    change (u t w : w.adicCompletion E) = z t w - x w
    simp only [u, dif_pos (ht w)]
  have := (tendsto_const_nhds (x := x)).add hv'
  simpa using this

theorem tendsto_ad {ι : Type} {l : Filter ι} (y : Ad E) (z : ι → Ad E) (h1 : ∀ t, (z t).1 = y.1)
    (h2 : Tendsto (fun t => (z t).2) l (𝓝 y.2)) : Tendsto z l (𝓝 y) := by
  refine (Prod.tendsto_iff _ _).2 ⟨?_, h2⟩
  simp only [h1]
  exact tendsto_const_nhds

theorem tendsto_gl {ι : Type} {l : Filter ι} (x : GA E a) (z : ι → GA E a)
    (h1 : ∀ i j, Tendsto (fun t => (z t).val i j) l (𝓝 (x.val i j)))
    (h2 : ∀ i j, Tendsto (fun t => (z t)⁻¹.val i j) l (𝓝 (x⁻¹.val i j))) : Tendsto z l (𝓝 x) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine Tendsto.prodMk_nhds ?_ ?_
  · exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => h1 i j
  · exact (MulOpposite.continuous_op.tendsto _).comp
      (tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => h2 i j)

variable [_root_.NumberField.IsTotallyComplex E]

theorem tendsto_entry (S : Finset (Pl E)) (x : GA E a) (z : Finset (Pl E) → GA E a)
    (hinf : ∀ T, cInf (z T) = cInf x) (hloc : ∀ T w, (w ∈ S ∨ w ∈ T) → cLoc w (z T) = cLoc w x)
    (hone : ∀ T w, w ∉ S → w ∉ T → cLoc w (z T) = 1) (i j : Fin a) :
    Tendsto (fun T => (z T).val i j) atTop (𝓝 (x.val i j)) := by
  classical
  refine tendsto_ad _ _ (fun T => ?_) (tendsto_af _ _ (fun w => ?_) ?_)
  · have h := congrArg (fun m : GL (Fin a) (Cinf E) => m.val i j) (hinf T)
    exact (infEq E).symm.injective h
  · filter_upwards [eventually_ge_atTop {w}] with T hT
    exact congrArg (fun m : GL (Fin a) (w.adicCompletion E) => m.val i j)
      (hloc T w (Or.inr (hT (Finset.mem_singleton_self w))))
  · have hx : ∀ᶠ w in cofinite, (x.val i j).2 w ∈ w.adicCompletionIntegers E := (x.val i j).2.2
    set F := (Filter.eventually_cofinite.1 hx).toFinset
    filter_upwards [eventually_ge_atTop F] with T hT w
    by_cases hw : w ∈ S ∨ w ∈ T
    · have h := congrArg (fun m : GL (Fin a) (w.adicCompletion E) => m.val i j) (hloc T w hw)
      change ((z T).val i j).2 w = (x.val i j).2 w at h
      rw [h, sub_self]
      exact zero_mem _
    · rw [not_or] at hw
      have h := congrArg (fun m : GL (Fin a) (w.adicCompletion E) => m.val i j) (hone T w hw.1 hw.2)
      change ((z T).val i j).2 w = (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j at h
      have hwF : w ∉ F := fun h' => hw.2 (hT h')
      have hxw : (x.val i j).2 w ∈ w.adicCompletionIntegers E := by
        by_contra hc
        exact hwF ((Filter.eventually_cofinite.1 hx).mem_toFinset.2 hc)
      refine sub_mem ?_ hxw
      rw [h, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _

theorem step1 (hG : G0) (S : Finset (Pl E)) (f : GA E a → ℂ)
    (hf : ∀ w, w ∉ S → ∀ h, cLoc w h = 1 → f h = 0 → ∀ u, f (h * fl a w u) = 0)
    (g g₀ : GA E a) (hinf : cInf g₀ = cInf g) (hS : ∀ w ∈ S, cLoc w g₀ = cLoc w g) (hIn : InS S g₀)
    (h0 : f g₀ = 0) (T : Finset (Pl E)) :
    ∃ h : GA E a, f h = 0 ∧ cInf h = cInf g ∧ (∀ w, (w ∈ S ∨ w ∈ T) → cLoc w h = cLoc w g) ∧
      (∀ w, w ∉ S → w ∉ T → cLoc w h = 1) := by
  classical
  obtain ⟨-, -, h3, h4, h5, -⟩ := hG E a
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨g₀, h0, hinf, fun w hw => ?_, fun w hw _ => hIn w hw⟩
    rcases hw with hw | hw
    · exact hS w hw
    · simp at hw
  | insert w T hwT ih =>
    obtain ⟨h, hf0, hi, hl, ho⟩ := ih
    by_cases hwS : w ∈ S
    · refine ⟨h, hf0, hi, fun v hv => ?_, fun v hv hv' => ho v hv fun h' => hv' (Finset.mem_insert_of_mem h')⟩
      rcases hv with hv | hv
      · exact hl v (Or.inl hv)
      · rcases Finset.mem_insert.1 hv with rfl | hv
        · exact hl v (Or.inl hwS)
        · exact hl v (Or.inr hv)
    · refine ⟨h * fl a w (cLoc w g), hf w hwS h (ho w hwS hwT) hf0 _, ?_, fun v hv => ?_, fun v hv hv' => ?_⟩
      · rw [map_mul, h3, mul_one, hi]
      · rw [map_mul]
        by_cases hvw : v = w
        · subst hvw
          rw [h4, ho v hwS hwT, one_mul]
        · rw [h5 _ _ _ hvw, mul_one]
          rcases hv with hv | hv
          · exact hl v (Or.inl hv)
          · exact hl v (Or.inr ((Finset.mem_insert.1 hv).resolve_left hvw))
      · have hvw : v ≠ w := fun e => hv' (e ▸ Finset.mem_insert_self w T)
        rw [map_mul, h5 _ _ _ hvw, mul_one]
        exact ho v hv fun h' => hv' (Finset.mem_insert_of_mem h')

end GeneralLinearEntryConvergence

open GeneralLinearEntryConvergence in
theorem convergence_entries_general_linear : G0 → PlacewiseToOutsideS := by
  intro hG E _ _ _ a S f hfc hf g g₀ hinf hS hIn h0
  choose H hH using step1 hG S f hf g g₀ hinf hS hIn h0
  have hT : Tendsto H atTop (𝓝 g) := by
    refine tendsto_gl g H (tendsto_entry S g H (fun T => (hH T).2.1) (fun T => (hH T).2.2.1)
      (fun T => (hH T).2.2.2)) (tendsto_entry S g⁻¹ (fun T => (H T)⁻¹) (fun T => ?_) (fun T w hw => ?_)
      (fun T w hw hw' => ?_))
    · rw [map_inv, map_inv, (hH T).2.1]
    · rw [map_inv, map_inv, (hH T).2.2.1 w hw]
    · rw [map_inv, (hH T).2.2.2 w hw hw', inv_one]
  have h1 := (hfc.tendsto g).comp hT
  have h2 : Tendsto (f ∘ H) atTop (𝓝 0) := by
    have e : f ∘ H = fun _ => 0 := funext fun T => (hH T).1
    rw [e]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

end PositivityTheory.jumpWindows

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace SmoothVectorOrbit

theorem orb_smul {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (c : ℂ) (v : X) :
    orb ρ (c • v) = c • orb ρ v := by
  funext M
  simp only [PositivityTheory.jumpWindows.orb, Pi.smul_apply]
  split_ifs <;> simp

theorem smV_smul {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (c : ℂ) (v : X) (h : SmV ρ v) : SmV ρ (c • v) := by
  unfold PositivityTheory.jumpWindows.SmV at h ⊢
  rw [PositivityTheory.jumpWindows.SmoothVectorOrbit.orb_smul]
  exact h.const_smul c

end SmoothVectorOrbit

theorem smooth_vector_orbit_invariance : G0 → G5 → G5b → G9 → PlacewiseToOutsideS → G8 := by
  intro hAC hSW hSP hWS hWV
  unfold PositivityTheory.jumpWindows.G8 PositivityTheory.jumpWindows.ForE
  intro E _ _ _ a ψ hψ S hS Y hY φ hφY hφ0 hφsm hφsph hφeig
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hreg, -⟩ := hAC E a
  obtain ⟨hΛ, htr, -, hW⟩ := hSW E a ψ hψ
  obtain ⟨hsmooth, hsph, hsph_smul, -, -⟩ := hSP E a S
  obtain ⟨-, hYtr, hYmir⟩ := hY
  obtain ⟨hWcont, hWne, -⟩ := hW φ (hYmir φ hφY)
  obtain ⟨g, hg⟩ := hWne hφ0
  obtain ⟨g₀, harch, hloc, hsupp⟩ := hreg S g
  have hg₀ : PositivityTheory.jumpWindows.Wh ψ φ g₀ ≠ 0 := by
    intro h0
    refine hg (hWV E a S _ hWcont ?_ g g₀ harch hloc hsupp h0)
    intro w hw h hh h0' u
    obtain ⟨B, hB⟩ := hφeig w hw
    exact hWS E a ψ hψ w (hS w hw) B φ (hYmir φ hφY) hB h hh h0' u
  have hφ'Y : PositivityTheory.jumpWindows.Rt E a g₀ φ ∈ Y := hYtr g₀ hsupp φ hφY
  have hW1 : PositivityTheory.jumpWindows.Wh ψ (PositivityTheory.jumpWindows.Rt E a g₀ φ) 1 ≠ 0 := by
    rw [htr, one_mul]
    exact hg₀
  refine ⟨(PositivityTheory.jumpWindows.Wh ψ (PositivityTheory.jumpWindows.Rt E a g₀ φ) 1)⁻¹ •
      PositivityTheory.jumpWindows.Rt E a g₀ φ, Y.smul_mem _ hφ'Y, ?_, ?_, ?_⟩
  · exact PositivityTheory.jumpWindows.SmoothVectorOrbit.smV_smul _ _ _ (hsmooth g₀ φ hφsm)
  · exact hsph_smul _ _ (hsph g₀ φ hφsph)
  · obtain ⟨Λ, hΛ1⟩ := hΛ 1
    rw [← hΛ1 _ (hYmir _ (Y.smul_mem _ hφ'Y)), map_smul, hΛ1 _ (hYmir _ hφ'Y), smul_eq_mul,
      inv_mul_cancel₀ hW1]

end PositivityTheory.jumpWindows

end
end
