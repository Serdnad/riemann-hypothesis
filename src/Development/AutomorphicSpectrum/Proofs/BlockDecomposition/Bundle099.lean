module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle077
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle078
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle079
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle080
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclicAlgebraHilbertNinety
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
open GlobalTheory.CatH (face toLast)
universe w w' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.ReesDown

section
variable {R : Type} [CommRing R] {D : Type u} [Category.{v} D] {F : D ⥤ ModuleCat.{w} R} (Ψ : Flt F)

def ev (r : ℕ) (T : D) : Ψ.Pr T →+ F.obj T where
  toFun x := (x r).1
  map_zero' := rfl
  map_add' _ _ := rfl

def cmp (r j : ℕ) (f : Cn Ψ.rees j) : Cn F j := fun s => ev Ψ r _ (f s)

def cmpS (r j : ℕ) (f : Cn Ψ.rees j) : Cn (Ψ.S r).fn j := fun s => (show Ψ.Pr _ from f s) r

def put (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) (z : Cn F j) : Cn Ψ.rees j := fun s =>
  show Ψ.Pr _ from fun r => match r with
    | 0 => ⟨z s, by rw [h0]; trivial⟩
    | _ + 1 => 0

theorem cmp_d (r j : ℕ) (f : Cn Ψ.rees j) : cmp Ψ r (j + 1) (d Ψ.rees j f) = d F j (cmp Ψ r j f) := by
  funext s
  refine (map_sum (ev Ψ r _) _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_zsmul]
  rfl

theorem cmp_zero (r j : ℕ) : cmp Ψ r j 0 = 0 := rfl

theorem cmp_sub (r j : ℕ) (f g : Cn Ψ.rees j) : cmp Ψ r j (f - g) = cmp Ψ r j f - cmp Ψ r j g := rfl

theorem cmp_put_zero (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) (z : Cn F j) : cmp Ψ 0 j (put Ψ h0 j z) = z := rfl

theorem cmp_put_succ (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (r j : ℕ) (z : Cn F j) : cmp Ψ (r + 1) j (put Ψ h0 j z) = 0 := rfl

theorem cochain_ext {j : ℕ} {f g : Cn Ψ.rees j} (h : ∀ r, cmp Ψ r j f = cmp Ψ r j g) : f = g := by
  funext s
  refine funext fun r => Subtype.ext ?_
  exact congrFun (h r) s

theorem put_d (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) (z : Cn F j) :
    d Ψ.rees j (put Ψ h0 j z) = put Ψ h0 (j + 1) (d F j z) := by
  refine cochain_ext Ψ fun r => ?_
  rw [cmp_d]
  cases r with
  | zero => rfl
  | succ r =>
    rw [cmp_put_succ, cmp_put_succ, map_zero]

theorem put_zero (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) : put Ψ h0 j 0 = 0 := by
  refine cochain_ext Ψ fun r => ?_
  cases r <;> rfl

theorem cmp_X (j r : ℕ) (f : Cn Ψ.rees j) : cmp Ψ (r + 1) j ((X : ℤ[X]) • f) = Ψ.μ • cmp Ψ r j f := by
  funext s
  exact Ψ.X_smul_succ _ (f s) r

theorem cmp_X_pow (j k : ℕ) (f : Cn Ψ.rees j) : cmp Ψ k j ((X : ℤ[X]) ^ k • f) = Ψ.μ ^ k • cmp Ψ 0 j f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_smul, cmp_X, ih, pow_succ', mul_smul]

theorem cmp_mem_B (r j : ℕ) (a : Cn Ψ.rees j) (h : a ∈ (cx Ψ.rees).B j) : cmp Ψ r j a ∈ (cx F).B j := by
  cases j with
  | zero =>
    have : a = 0 := h
    rw [this]
    exact Submodule.zero_mem _
  | succ j =>
    obtain ⟨e, rfl⟩ := h
    exact ⟨cmp Ψ r j e, (cmp_d Ψ r j e).symm⟩

theorem put_mem_B (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) (a : Cn F j) (h : a ∈ (cx F).B j) :
    put Ψ h0 j a ∈ (cx Ψ.rees).B j := by
  cases j with
  | zero =>
    have : a = 0 := h
    rw [this, put_zero]
    exact Submodule.zero_mem _
  | succ j =>
    obtain ⟨e, rfl⟩ := h
    exact ⟨put Ψ h0 j e, put_d Ψ h0 j e⟩

theorem d_cmpS (r j : ℕ) (f : Cn Ψ.rees j) (hf : d Ψ.rees j f = 0) : d (Ψ.S r).fn j (cmpS Ψ r j f) = 0 := by
  funext s
  refine Subtype.ext ?_
  have h1 := congrFun ((Ψ.S r).inc.d_pullC j (cmpS Ψ r j f)) s
  have h2 : d F j (cmp Ψ r j f) = 0 := by rw [← cmp_d, hf, cmp_zero]
  exact h1.symm.trans (congrFun h2 s)

end

end GlobalTheory.CompanionTheory.ReesDown

namespace GlobalTheory.CompanionTheory.ReesDown

theorem put_pull {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {F : C ⥤ ModuleCat.{w} R} (Φ : Flt F) (G : C' ⥤ C) (h0 : ∀ T, (Φ.S 0).S T = ⊤) (j : ℕ) (z : Cn F j) :
    (Mor.restrict Φ.rees G).pullC j (put Φ h0 j z) =
      put (Φ.comap G) (fun T => h0 (G.obj T)) j ((Mor.restrict F G).pullC j z) := by
  refine cochain_ext (Φ.comap G) fun r => ?_
  cases r <;> rfl

theorem main : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} (Φ : Flt F) (G : C' ⥤ C) (n N : ℕ), (∀ T, (Φ.S 0).S T = ⊤) → RI ((X : ℤ[X]) ^ N) n Φ.rees G → ∀ j ≤ n, InjUpTo (Φ.μ ^ N) ((Mor.restrict F G).pull j) ∧ ∀ y, ∃ x ∈ (Φ.S N).img j, (Mor.restrict F G).pull j x = Φ.μ ^ N • y := by
  intro R _ C _ C' _ F Φ G n N h0 hRI j hj
  have hU : UpTo ((X : ℤ[X]) ^ N) ((Mor.restrict Φ.rees G).pull j) := hRI j hj
  have h0' : ∀ T, ((Φ.comap G).S 0).S T = ⊤ := fun T => h0 (G.obj T)
  have hpd : ∀ (z : Cn F j), d F j z = 0 → d (G ⋙ F) j ((Mor.restrict F G).pullC j z) = 0 := fun z hz => by
    rw [Mor.d_pullC, hz, map_zero]
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := (P.cls_surj (cx F) j).1 x
    have h2 : (Mor.restrict F G).pullC j z ∈ (cx (G ⋙ F)).B j := by
      have h1 := P.mapH_cls (Mor.restrict F G).hom j z hz (hpd z hz)
      exact ((P.cls_surj (cx (G ⋙ F)) j).2.1 _ _).1 (h1.symm.trans hx)
    have hZ : d Φ.rees j (put Φ h0 j z) = 0 := by
      rw [put_d, hz]; exact put_zero Φ h0 _
    have hZ' : d (G ⋙ Φ.rees) j ((Mor.restrict Φ.rees G).pullC j (put Φ h0 j z)) = 0 := by
      rw [Mor.d_pullC, hZ, map_zero]
    have h3 : (Mor.restrict Φ.rees G).pull j ((cx Φ.rees).cls _ hZ) = 0 := by
      refine (P.mapH_cls (Mor.restrict Φ.rees G).hom j _ hZ hZ').trans ?_
      refine ((P.cls_surj (cx (G ⋙ Φ.rees)) j).2.1 _ _).2 ?_
      have key : ∀ a : (cx (G ⋙ Φ.rees)).X j, a = put (Φ.comap G) h0' j ((Mor.restrict F G).pullC j z) →
          a ∈ (cx (G ⋙ Φ.rees)).B j := by
        intro a ha
        subst ha
        exact put_mem_B (Φ.comap G) h0' j _ h2
      exact key _ (put_pull Φ G h0 j z)
    have hXZ : d Φ.rees j ((X : ℤ[X]) ^ N • put Φ h0 j z) = 0 := by
      rw [map_smul, hZ, smul_zero]
    have h4 := hU.1 _ h3
    rw [← (P.cls_surj (cx Φ.rees) j).2.2.2.2 _ _ hZ hXZ] at h4
    have h5 := cmp_mem_B Φ N j _ (((P.cls_surj (cx Φ.rees) j).2.1 _ hXZ).1 h4)
    rw [cmp_X_pow, cmp_put_zero] at h5
    have hμ : d F j (Φ.μ ^ N • z) = 0 := by rw [map_smul, hz, smul_zero]
    rw [← (P.cls_surj (cx F) j).2.2.2.2 _ _ hz hμ]
    exact ((P.cls_surj (cx F) j).2.1 _ hμ).2 h5
  · obtain ⟨w, hw, rfl⟩ := (P.cls_surj (cx (G ⋙ F)) j).1 y
    have hW : d (G ⋙ Φ.rees) j (put (Φ.comap G) h0' j w) = 0 := by
      refine (put_d (Φ.comap G) h0' j w).trans ?_
      rw [hw]; exact put_zero (Φ.comap G) h0' _
    obtain ⟨x', hx'⟩ := hU.2 ((cx (G ⋙ Φ.rees)).cls (show (cx (G ⋙ Φ.rees)).X j from put (Φ.comap G) h0' j w) hW)
    obtain ⟨Z, hZ, rfl⟩ := (P.cls_surj (cx Φ.rees) j).1 x'
    have hZ' : d (G ⋙ Φ.rees) j ((Mor.restrict Φ.rees G).pullC j Z) = 0 := by
      rw [Mor.d_pullC, hZ, map_zero]
    have hXW : d (G ⋙ Φ.rees) j ((X : ℤ[X]) ^ N • put (Φ.comap G) h0' j w) = 0 := by
      rw [map_smul, hW, smul_zero]
    have hx2 := (P.mapH_cls (Mor.restrict Φ.rees G).hom j Z hZ hZ').symm.trans hx'
    rw [← (P.cls_surj (cx (G ⋙ Φ.rees)) j).2.2.2.2 _ _ hW hXW] at hx2
    have hB := ((P.cls_surj (cx (G ⋙ Φ.rees)) j).2.2.1 _ _ hZ' hXW).1 hx2
    have hc : (Mor.restrict F G).pullC j (cmp Φ N j Z) - Φ.μ ^ N • w ∈ (cx (G ⋙ F)).B j := by
      have h := cmp_mem_B (Φ.comap G) N j _ hB
      have e : ∀ A : Cn (Φ.comap G).rees j, A = (Mor.restrict Φ.rees G).pullC j Z →
          cmp (Φ.comap G) N j (A - (X : ℤ[X]) ^ N • put (Φ.comap G) h0' j w) =
            (Mor.restrict F G).pullC j (cmp Φ N j Z) - Φ.μ ^ N • w := by
        intro A hA
        rw [cmp_sub, cmp_X_pow, cmp_put_zero, hA]
        rfl
      exact (e _ rfl) ▸ h
    have hz0 : d F j (cmp Φ N j Z) = 0 := by rw [← cmp_d, hZ, cmp_zero]
    have hμ : d (G ⋙ F) j (Φ.μ ^ N • w) = 0 := by rw [map_smul, hw, smul_zero]
    refine ⟨(cx F).cls _ hz0, ⟨(cx (Φ.S N).fn).cls _ (d_cmpS Φ N j Z hZ), ?_⟩, ?_⟩
    · exact P.mapH_cls (Φ.S N).inc.hom j _ _ hz0
    · refine (P.mapH_cls (Mor.restrict F G).hom j _ hz0 (hpd _ hz0)).trans ?_
      rw [← (P.cls_surj (cx (G ⋙ F)) j).2.2.2.2 _ _ hw hμ]
      exact ((P.cls_surj (cx (G ⋙ F)) j).2.2.1 _ _ _ hμ).2 hc

end GlobalTheory.CompanionTheory.ReesDown
end

section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisCross

theorem sec_inv {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {w : W} (hP : IsPar Γ K P c)
    (law : ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w) :
    ∀ γ ∈ Γ, γ ∈ P → ∀ x, sec K P c ρ (γ * x) w = sec K P c ρ x w := by
  intro γ hγ hγP x
  obtain ⟨p, hp, k, hk, rfl⟩ := hP.iwa x
  have h1 := law (γ * p) (P.mul_mem hγP hp) ⟨k, hk⟩
  have h2 := law p hp ⟨k, hk⟩
  simp only at h1 h2
  rw [← mul_assoc, h1, h2, hP.ch.mul γ hγP p hp, hP.ch.rat γ hγ hγP, one_mul]

theorem cross (hSec : SecLaw) (hHt : HtLip) (hSt : PiLocalization₂) (hWL : WallLaw) : Cross := by
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ Γ Q P P' c η η' β ξ L R D Op H Ω hPQ hP'Q hP hP' hη hη' hβ hξ hW hΩ hx
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have parRes : ∀ (P : Subgroup G), IsPar Γ K P c → IsPar (Γ ⊓ Q) K P c := fun _ h =>
    ⟨h.closed, h.iwa, ⟨h.ch.mul, h.ch.norm, fun γ hγ hp => h.ch.rat γ hγ.1 hp, h.ch.cont⟩⟩
  have htRes : ∀ (P : Subgroup G) (f : G → ℝ), IsHt Γ K P f → IsHt (Γ ⊓ Q) K P f := fun _ _ h =>
    ⟨h.left, h.right, fun γ hγ hp => h.rat γ hγ.1 hp, h.cont⟩
  obtain ⟨-, -, hbound⟩ := hWL G W K ρ hK hρ (Γ ⊓ Q) P P' c η η' β L R D Op H (parRes P hP) (parRes P' hP')
    (htRes P η hη) (htRes P' η' hη') (htRes P' β hβ) hW
  have hξinv : ∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x := by
    intro γ h1 h2 x
    rw [hξ.left γ h2, hξ.rat γ h1 h2, zero_add]
  have htinv : ∀ (P : Subgroup G) (f : G → ℝ), IsHt Γ K P f → ∀ γ ∈ Γ, γ ∈ P → ∀ x, f (γ * x) = f x := by
    intro P f hf γ h1 h2 x
    rw [hf.left γ h2, hf.rat γ h1 h2, zero_add]
  have iwaQ : Iwa Q K := fun g => by
    obtain ⟨p, hp, k, hk, e⟩ := hP.iwa g
    exact ⟨p, hPQ hp, k, hk, e⟩
  have mξ := hHt G Γ K Q ξ hK iwaQ hξ
  have mη := hHt G Γ K P η hK hP.iwa hη
  have mη' := hHt G Γ K P' η' hK hP'.iwa hη'
  have mβ := hHt G Γ K P' β hK hP'.iwa hβ
  let t : Cos (Γ ⊓ Q) Γ → ℂ × ℂ → G → (L →L[ℂ] W) := fun r l g =>
    Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g)
  have hhol : ∀ r g (p v : ℂ × ℂ), Differentiable ℂ fun τ : ℂ => t r (p + τ • v) g := by
    intro r g p v
    have h1 : Differentiable ℂ fun τ : ℂ => H (p + τ • v).1 (rep r * g) :=
      (hW.hol (rep r * g)).comp (by fun_prop)
    have h2 : Differentiable ℂ fun τ : ℂ => Complex.exp ((p + τ • v).2 * ξ (rep r * g)) := by fun_prop
    exact h2.smul h1
  have hcont : ∀ r, Continuous fun y : (ℂ × ℂ) × G => t r y.1 y.2 := by
    intro r
    have h0 : Continuous fun y : (ℂ × ℂ) × G => rep r * y.2 := by fun_prop
    have h1 : Continuous fun y : (ℂ × ℂ) × G => H y.1.1 (rep r * y.2) :=
      hW.cont.comp (continuous_fst.fst.prodMk h0)
    have h2 : Continuous fun y : (ℂ × ℂ) × G => ξ (rep r * y.2) := hξ.cont.comp h0
    have h3 : Continuous fun y : (ℂ × ℂ) × G => Complex.exp (y.1.2 * ξ (rep r * y.2)) :=
      Complex.continuous_exp.comp ((continuous_fst.snd).mul (Complex.continuous_ofReal.comp h2))
    exact h3.smul h1
  have hdom : ∀ x ∈ Ω, ∀ g, ∃ V ∈ 𝓝 x, ∃ U ∈ 𝓝 g, ∃ u : Cos (Γ ⊓ Q) Γ → ℝ, Summable u ∧
      ∀ l ∈ tube V, ∀ g' ∈ U, ∀ r, ‖t r l g'‖ ≤ u r := by
    intro x hxΩ g
    obtain ⟨a, b, ε, hε, hRa, hbR, hbx, hxa, hconv⟩ := hx x hxΩ
    obtain ⟨M, hM⟩ := hbound a b hRa hbR
    have inv₁ : ∀ γ ∈ Γ, γ ∈ P → ∀ x, (fun x => a * η x) (γ * x) = (fun x => a * η x) x := by
      intro γ h1 h2 x
      simp only [htinv P η hη γ h1 h2 x]
    have inv₂ : ∀ γ ∈ Γ, γ ∈ P' → ∀ x, (fun x => β x - b * η' x) (γ * x) = (fun x => β x - b * η' x) x := by
      intro γ h1 h2 x
      simp only [htinv P' η' hη' γ h1 h2 x, htinv P' β hβ γ h1 h2 x]
    have m₁ : ∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |a * η (g * u) - a * η g| ≤ A := by
      intro C hC
      obtain ⟨A, hA⟩ := mη C hC
      refine ⟨|a| * A, fun g u hu => ?_⟩
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hA g u hu) (abs_nonneg a)
    have m₂ : ∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C,
        |(β (g * u) - b * η' (g * u)) - (β g - b * η' g)| ≤ A := by
      intro C hC
      obtain ⟨A, hA⟩ := mη' C hC
      obtain ⟨B, hB⟩ := mβ C hC
      refine ⟨B + |b| * A, fun g u hu => ?_⟩
      have e : (β (g * u) - b * η' (g * u)) - (β g - b * η' g) =
          (β (g * u) - β g) - b * (η' (g * u) - η' g) := by ring
      rw [e]
      refine (abs_sub _ _).trans (add_le_add (hB g u hu) ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hA g u hu) (abs_nonneg b)
    have hl : |x.2 - ε - x.2| ≤ ε := by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hε]
    have hr : |x.2 + ε - x.2| ≤ ε := by rw [add_sub_cancel_left, abs_of_pos hε]
    obtain ⟨U, hU, u, hu, hb⟩ := GlobalTheory.T.coarse_lipschitz_exponential_estimate G (L →L[ℂ] W) Γ (Γ ⊓ Q) P P' ξ (fun x => a * η x) (fun x => β x - b * η' x) H a b
      (x.2 - ε) (x.2 + ε) M mξ m₁ m₂ (hW.convR a hRa) (hW.convL b hbR) hM
      (GlobalTheory.T.coset_series_summable_shifted hSt G Γ Q P ξ _ _ hPQ hξinv inv₁ (hconv _ hl).1)
      (GlobalTheory.T.coset_series_summable_shifted hSt G Γ Q P ξ _ _ hPQ hξinv inv₁ (hconv _ hr).1)
      (GlobalTheory.T.coset_series_summable_shifted hSt G Γ Q P' ξ _ _ hP'Q hξinv inv₂ (hconv _ hl).2)
      (GlobalTheory.T.coset_series_summable_shifted hSt G Γ Q P' ξ _ _ hP'Q hξinv inv₂ (hconv _ hr).2) g
    refine ⟨Set.Icc b a ×ˢ Set.Icc (x.2 - ε) (x.2 + ε),
      prod_mem_nhds (Icc_mem_nhds hbx hxa) (Icc_mem_nhds (by linarith) (by linarith)), U, hU, u, hu, ?_⟩
    intro l hl g' hg' r
    obtain ⟨h1, h2⟩ := hl
    exact hb l h1.1 h1.2 h2.1 h2.2 g' hg' r
  obtain ⟨hTG, hsum⟩ := GlobalTheory.T.holomorphic_series_uniform_tube _ _ _ t Ω hhol hcont hdom
  have key : ∀ l ∈ tube Ω, ∀ g (w : L), outer Γ (Γ ⊓ Q) ξ H l g w =
      ∑' r : Cos (Γ ⊓ Q) Γ, Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g) w := by
    intro l hl g w
    have hs : Summable fun r => t r l g := (hsum l hl g).of_norm
    exact (ContinuousLinearMap.apply ℂ W w).map_tsum hs
  obtain ⟨law, -, Ms, hMs⟩ := hSec G W K ρ hK hρ Γ P c hP
  obtain ⟨law', -, Ms', hMs'⟩ := hSec G W K ρ hK hρ Γ P' c hP'
  refine ⟨hTG, hsum, ?_, ?_⟩
  · intro l hl hRl hconv g w
    have hw : (w : W) ∈ secSp K P c ρ := hW.le w.2
    rw [key l hl g w]
    have e : ∀ r : Cos (Γ ⊓ Q) Γ, Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g) w =
        D l.1 • (Complex.exp (l.2 * ξ (rep r * g)) •
          eis (Γ ⊓ Q) K P c ρ (fun x => l.1 * η x) (rep r * g) w) := by
      intro r
      rw [hW.eqR l.1 hRl, smul_comm]
    simp_rw [e]
    rw [tsum_const_smul'']
    congr 1
    refine GlobalTheory.T.section_invariance_coset_sum hSt G W Γ K Q P c ρ ξ (fun x => l.1.re * η x + l.2.re * ξ x) (fun x => l.1 * η x) l.2 w
      (Ms * ‖(w : W)‖) hPQ hξinv ?_ (sec_inv hP (law w hw)) (fun x => hMs x w) hconv ?_ g
    · intro γ h1 h2 x
      simp only [htinv P η hη γ h1 h2 x]
    · intro x
      simp
  · intro l hl hRl hconv g w
    have hw : ((Op l.1 w : secSp K P' c ρ) : W) ∈ secSp K P' c ρ := (Op l.1 w).2
    rw [key l hl g w]
    have e : ∀ r : Cos (Γ ⊓ Q) Γ, Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g) w =
        Complex.exp (l.2 * ξ (rep r * g)) •
          eis (Γ ⊓ Q) K P' c ρ (fun x => β x - l.1 * η' x) (rep r * g) (Op l.1 w) := by
      intro r
      rw [hW.eqL l.1 hRl]
    simp_rw [e]
    refine GlobalTheory.T.section_invariance_coset_sum hSt G W Γ K Q P' c ρ ξ (fun x => β x - l.1.re * η' x + l.2.re * ξ x)
      (fun x => (β x : ℂ) - l.1 * η' x) l.2 _ (Ms' * ‖((Op l.1 w : secSp K P' c ρ) : W)‖) hP'Q hξinv ?_
      (sec_inv hP' (law' _ hw)) (fun x => hMs' x _) hconv ?_ g
    · intro γ h1 h2 x
      simp only [htinv P' η' hη' γ h1 h2 x, htinv P' β hβ γ h1 h2 x]
    · intro x
      simp

end GlobalTheory.CompanionTheory.RgEisCross
end

section


theorem _root_.GlobalTheory.T.hecke_third_property : PositivityTheory.Rg.Tf.Loc.H3 := by
  first | exact @GlobalTheory.CompanionTheory.TwistedCent.h3 | exact GlobalTheory.CompanionTheory.TwistedCent.h3 | (intros; apply GlobalTheory.CompanionTheory.TwistedCent.h3 <;> assumption)
end

section


theorem _root_.GlobalTheory.T.lattice_first_property : PositivityTheory.Rg.Tf.Loc.L1 := by
  first | exact @GlobalTheory.CompanionTheory.LatticeCoset.latticeOf_eq_iff | exact GlobalTheory.CompanionTheory.LatticeCoset.latticeOf_eq_iff | (intros; apply GlobalTheory.CompanionTheory.LatticeCoset.latticeOf_eq_iff <;> assumption)
end

section


theorem _root_.GlobalTheory.T.norm_commutes_separable_holds : PositivityTheory.Rg.Tf.Loc.A1 → PositivityTheory.Rg.Tf.Loc.A2 := by
  first | exact @GlobalTheory.CompanionTheory.TfLoc.norm_commutes_of_separable | exact GlobalTheory.CompanionTheory.TfLoc.norm_commutes_of_separable | (intros; apply GlobalTheory.CompanionTheory.TfLoc.norm_commutes_of_separable <;> assumption)
end

section


theorem _root_.GlobalTheory.T.unit_fundamental_lemma_second_holds : PositivityTheory.Rg.Tf.Loc.L2 → PositivityTheory.Rg.Tf.Loc.N4 → PositivityTheory.Rg.Tf.Loc.Z2 := by
  first | exact @GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_second | exact GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_second | (intros; apply GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_second <;> assumption)
end

section


theorem _root_.GlobalTheory.T.lattice_second_property : PositivityTheory.Rg.Tf.Loc.D0a → PositivityTheory.Rg.Tf.Loc.L2 := by
  first | exact @GlobalTheory.CompanionTheory.Tf.Loc.stableLattice_unitIntegral | exact GlobalTheory.CompanionTheory.Tf.Loc.stableLattice_unitIntegral | (intros; apply GlobalTheory.CompanionTheory.Tf.Loc.stableLattice_unitIntegral <;> assumption)
end

section


theorem _root_.GlobalTheory.T.norm_map_second_property : PositivityTheory.Rg.Tf.Loc.N2 := by
  first | exact @GlobalTheory.CompanionTheory.NormLoc.fixedRing_traceOne_firstOrder | exact GlobalTheory.CompanionTheory.NormLoc.fixedRing_traceOne_firstOrder | (intros; apply GlobalTheory.CompanionTheory.NormLoc.fixedRing_traceOne_firstOrder <;> assumption)
end

section


theorem _root_.GlobalTheory.T.separable_norm_commuting : PositivityTheory.Rg.Tf.Loc.A1 := by
  first | exact @GlobalTheory.CompanionTheory.Centraliser.a1 | exact GlobalTheory.CompanionTheory.Centraliser.a1 | (intros; apply GlobalTheory.CompanionTheory.Centraliser.a1 <;> assumption)
end

section


theorem _root_.GlobalTheory.T.unipotent_hecke_fourth_property : PositivityTheory.Rg.Tf.Loc.D0a → PositivityTheory.Rg.Tf.Loc.T0 → PositivityTheory.Rg.Tf.Loc.A1 → PositivityTheory.Rg.Tf.Loc.MeasureTransportOpenSet := by
  first | exact @GlobalTheory.CompanionTheory.TfLoc.transport_open_trace | exact GlobalTheory.CompanionTheory.TfLoc.transport_open_trace | (intros; apply GlobalTheory.CompanionTheory.TfLoc.transport_open_trace <;> assumption)
end

section


theorem _root_.GlobalTheory.T.norm_map_torus_surjective : PositivityTheory.Rg.Tf.Loc.T0 := by
  first | exact @GlobalTheory.CompanionTheory.LocTop.t0 | exact GlobalTheory.CompanionTheory.LocTop.t0 | (intros; apply GlobalTheory.CompanionTheory.LocTop.t0 <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.cyclic_algebra_hilbert_ninety : PositivityTheory.Rg.Tf.Loc.N1 → ∀ (O O' R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] [CommRing R] [Algebra O R] [Module.Finite O R] (ℓ : ℕ) (τ : O' ≃ₐ[O] O'), 0 < ℓ → τ ^ ℓ = 1 → (∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O')) → (∃ x y : Fin ℓ → O', ∀ j < ℓ, ∑ i, x i * (τ ^ j) (y i) = if j = 0 then 1 else 0) → (∃ a : O', ∑ j ∈ Finset.range ℓ, (τ ^ j) a = 1) → ∀ r : Rˣ, ∃ s : (O' ⊗[O] R)ˣ, (∏ j ∈ Finset.range ℓ, Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) (s : O' ⊗[O] R)) - (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) (r : R) ∈ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) (⊥ : Ideal R).jacobson := by
  first | exact @GlobalTheory.CompanionTheory.FirstApprox.main | exact GlobalTheory.CompanionTheory.FirstApprox.main | (intros; apply GlobalTheory.CompanionTheory.FirstApprox.main <;> assumption)
end
