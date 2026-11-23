module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle526
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl

@[expose] public section

section

noncomputable section

open Matrix MeasureTheory Polynomial
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.Tf.Loc
open GlobalTheory.BCT Formalism.BasicNotions

namespace GlobalTheory.CompanionTheory.LefPair

variable {n : ℕ}

local notation "θ" => thetaR (starRingEnd ℂ)

theorem tw_eq (x d : GL (Fin n) ℂ) : PositivityTheory.RgTw.tw x d = twConj (θ n) x d := by
  have h : PositivityTheory.RgTw.th x = θ n x := by
    apply Units.ext
    rfl
  simp only [PositivityTheory.RgTw.tw, twConj, h]

theorem theta_theta (g : GL (Fin n) ℂ) : θ n (θ n g) = g := by
  apply Units.ext
  show (((g.val.map (starRingEnd ℂ))ᵀ).map (starRingEnd ℂ))ᵀ = g.val
  ext i j
  simp

theorem twConj_twConj (g x d : GL (Fin n) ℂ) :
    twConj (θ n) x (twConj (θ n) g d) = twConj (θ n) (g * x) d := by
  simp only [twConj, map_mul]
  group

theorem theta_diag (d : GL (Fin n) ℂ) (z : Fin n → ℂ) (hd : d.val = diagonal z) (hz : ∀ i, ‖z i‖ = 1) :
    (θ n d).val = diagonal z := by
  have hz0 : ∀ i, z i ≠ 0 := fun i h => by simpa [h] using hz i
  have hinv : (d⁻¹).val = diagonal fun i => (z i)⁻¹ := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hd, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hz0 i)
  rw [thetaR_val, hinv]
  ext i j
  by_cases h : i = j
  · subst h
    simp only [transpose_apply, map_apply, diagonal_apply_eq]
    rw [Complex.inv_eq_conj (hz i), Complex.conj_conj]
  · simp [diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h)]

theorem charpoly_norm (g d : GL (Fin n) ℂ) (z : Fin n → ℂ) (hd : d.val = diagonal z) (hz : ∀ i, ‖z i‖ = 1) :
    (twConj (θ n) g d * θ n (twConj (θ n) g d)).val.charpoly = (diagonal fun i => z i ^ 2).charpoly := by
  have h : twConj (θ n) g d * θ n (twConj (θ n) g d) = g⁻¹ * (d * θ n d) * g := by
    simp only [twConj, map_mul, map_inv, theta_theta]
    group
  have h2 : (d * θ n d).val = diagonal fun i => z i ^ 2 := by
    rw [Units.val_mul, theta_diag d z hd hz, hd, diagonal_mul_diagonal]
    congr 1
    funext i
    exact (pow_two _).symm
  rw [h, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj', h2]

theorem locallyCompact_GL (n : ℕ) : LocallyCompactSpace (GL (Fin n) ℂ) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem secondCountable_GL (n : ℕ) : SecondCountableTopology (GL (Fin n) ℂ) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem sigmaFinite_haar [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
    (ν : Measure (GL (Fin n) ℂ)) [ν.IsHaarMeasure] : SigmaFinite ν := by
  have := locallyCompact_GL n
  have := secondCountable_GL n
  have : SigmaCompactSpace (GL (Fin n) ℂ) := sigmaCompactSpace_of_locallyCompact_secondCountable
  exact Measure.IsHaarMeasure.sigmaFinite ν

theorem lefOne_eval (hD : EllDiag) (hW : WeylAt) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
    (ν : Measure (GL (Fin n) ℂ)) [ν.IsHaarMeasure] (l : DomWeight n) (v : ℂ) (f : GL (Fin n) ℂ → ℂ)
    (h : LefOne ν l v f) (d : GL (Fin n) ℂ) (hd : EllC d) :
    ∫ x, f (twConj (θ n) x d) ∂ν = v * starRingEnd ℂ (chAt l (d * θ n d).val.charpoly) := by
  obtain ⟨g, d', z, hd', hz, hinj, rfl⟩ := hD n d hd
  have hz0 : ∀ i, z i ^ 2 ≠ 0 := fun i h0 => by
    have : z i = 0 := by simpa using h0
    simpa [this] using hz i
  simp_rw [twConj_twConj]
  rw [integral_mul_left_eq_self (fun y => f (twConj (θ n) y d')) g, charpoly_norm g d' z hd' hz,
    hW n l (fun i => z i ^ 2) hz0 hinj]
  have := h.2.2 d' z hd' hz hinj
  simp_rw [tw_eq] at this
  exact this

end GlobalTheory.CompanionTheory.LefPair


open GlobalTheory.CompanionTheory.LefPair in
theorem GlobalTheory.CompanionTheory.LefPair.lefPairOf : LefPairOf := by
  intro hD hW _ a b _ _ _ _ ν₁ _ ν₂ _ l₁ l₂ v₁ v₂ f₁ f₂ h₁ h₂
  have := sigmaFinite_haar ν₁
  have := sigmaFinite_haar ν₂
  refine ⟨(h₁.1.comp continuous_fst).mul (h₂.1.comp continuous_snd), ?_, fun d₁ d₂ e₁ e₂ => ?_⟩
  · refine HasCompactSupport.intro (h₁.2.1.prod h₂.2.1) fun x hx => ?_
    rw [Set.mem_prod, not_and_or] at hx
    rcases hx with hx | hx
    · simp [image_eq_zero_of_notMem_tsupport hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · rw [integral_prod_mul (fun x => f₁ (twConj (thetaR (starRingEnd ℂ) a) x d₁))
      (fun x => f₂ (twConj (thetaR (starRingEnd ℂ) b) x d₂)),
      lefOne_eval hD hW ν₁ l₁ v₁ f₁ h₁ d₁ e₁, lefOne_eval hD hW ν₂ l₂ v₂ f₂ h₂ d₂ e₂]
    ring

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

namespace GlobalTheory.CompanionTheory.TranslAdele

theorem thetaR_thetaR {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (n : ℕ)
    (g : GL (Fin n) A) : thetaR σ n (thetaR σ n g) = g := by
  apply Units.ext
  ext i j
  change σ (σ (g.val i j)) = g.val i j
  exact hσ _

theorem exists_scalar_of_central {K : Type} [Field K] {n : ℕ} (z : GL (Fin n) K)
    (hz : ∀ h : GL (Fin n) K, z * h = h * z) : ∃ c : K, z.val = Matrix.scalar (Fin n) c := by
  have : z.val ∈ Set.range (Matrix.scalar (Fin n) : K →+* Matrix (Fin n) (Fin n) K) := by
    apply Matrix.mem_range_scalar_of_commute_transvectionStruct
    intro t
    have h := hz ⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩
    have h' := congrArg Units.val h
    exact h'.symm
  obtain ⟨c, hc⟩ := this
  exact ⟨c, hc.symm⟩

theorem Phi_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    (GlobalTheory.Tw.Phi n R).map f = GlobalTheory.Tw.Phi n S := by
  ext i j
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem translAd : TranslAd := by
  intro E _ _ _ n u hu g

  have hz : ∀ h : GL (Fin n) E, ((PhiU n E)⁻¹ * u) * h = h * ((PhiU n E)⁻¹ * u) := by
    intro h
    have hinv : thetaE E n (thetaE E n h) = h :=
      thetaR_thetaR (conjE E) (fun x => IsCMField.complexConj_apply_apply E x) n h
    have h1 := hu.1 (thetaE E n h)
    rw [hinv] at h1
    have h2 : thE E n (thetaE E n h) = PhiU n E * h * (PhiU n E)⁻¹ := by
      have := thetaGL_eq n E (IsCMField.complexConj E).toRingEquiv.toRingHom (thetaE E n h)
      rw [show thetaR (IsCMField.complexConj E).toRingEquiv.toRingHom n (thetaE E n h) = h from hinv] at this
      exact this
    rw [h2] at h1
    have h3 : h * (PhiU n E)⁻¹ * u = (PhiU n E)⁻¹ * u * h := by
      have h4 : PhiU n E * h * (PhiU n E)⁻¹ * u = u * h := by rw [h1]; group
      calc h * (PhiU n E)⁻¹ * u = (PhiU n E)⁻¹ * (PhiU n E * h * (PhiU n E)⁻¹ * u) := by group
        _ = (PhiU n E)⁻¹ * u * h := by rw [h4]; group
    rw [← h3, mul_assoc h]
  obtain ⟨c, hc⟩ := exists_scalar_of_central _ hz

  set w : GA E n := ratGL E n ((PhiU n E)⁻¹ * u) with hw
  have hwc : ∀ t : GA E n, w * t = t * w := by
    intro t
    apply Units.ext
    have hval : w.val = Matrix.scalar (Fin n) (algebraMap E (Ad E) c) := by
      have : w.val = (((PhiU n E)⁻¹ * u : GL (Fin n) E).val).map (algebraMap E (Ad E)) := rfl
      rw [this, hc]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
    rw [Units.val_mul, Units.val_mul, hval]
    exact Matrix.scalar_commute _ (fun r' => Commute.all _ _) _
  have hP : ratGL E n (PhiU n E) = PhiU n (Ad E) := by
    apply Units.ext
    rw [phiU_val, ← Phi_map (algebraMap E (Ad E)) n, ← phiU_val]
    rfl
  have hr : ratGL E n u = PhiU n (Ad E) * w := by
    rw [hw, map_mul, map_inv, hP, mul_inv_cancel_left]
  rw [thetaGL_eq, hr]
  have h5 : w * thetaA E n g * w⁻¹ = thetaA E n g := by rw [hwc]; group
  calc PhiU n (Ad E) * thetaR (conjAd E) n g * (PhiU n (Ad E))⁻¹
      = PhiU n (Ad E) * (w * thetaA E n g * w⁻¹) * (PhiU n (Ad E))⁻¹ := by rw [h5]
    _ = PhiU n (Ad E) * w * thetaA E n g * (PhiU n (Ad E) * w)⁻¹ := by group

end GlobalTheory.CompanionTheory.TranslAdele

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace GlobalTheory.CompanionTheory.TwistCent

theorem map_thetaR {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R →+* R) (c' : S →+* S)
    (h : ∀ x, f (c x) = c' (f x)) (n : ℕ) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (thetaR c n g) = thetaR c' n (GeneralLinearGroup.map f g) := by
  apply Units.ext
  ext i j
  rw [GeneralLinearGroup.map_apply, thetaR_val, thetaR_val, ← map_inv]
  simp only [Matrix.transpose_apply, Matrix.map_apply, GeneralLinearGroup.map_apply, h]

theorem map_phiU {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    GeneralLinearGroup.map f (PhiU n R) = PhiU n S := by
  apply Units.ext
  ext i j
  simp only [GeneralLinearGroup.map_apply, phiU_val, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem map_thetaGL {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R →+* R) (c' : S →+* S)
    (h : ∀ x, f (c x) = c' (f x)) (n : ℕ) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (thetaGL n c g) = thetaGL n c' (GeneralLinearGroup.map f g) := by
  rw [thetaGL_eq, thetaGL_eq, map_mul, map_mul, map_inv, map_phiU, map_thetaR f c c' h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem thF_ratF (g : GL (Fin n) E) : thF E n (ratF E n g) = ratF E n (thE E n g) :=
  (map_thetaGL (algebraMap E (Af E)) _ _
    (fun x => (conjFin_algebraMap (IsCMField.complexConj E).toRingEquiv x).symm) n g).symm

theorem nontrivial_finiteAdeles : Nontrivial (Af E) := by
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal (𝓞 E)
  let v₀ : HeightOneSpectrum (𝓞 E) :=
    ⟨m₀, hm₀.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm₀ (RingOfIntegers.not_isField E)⟩
  exact ⟨⟨0, 1, fun h => zero_ne_one (congrArg (fun x : Af E => x v₀) h)⟩⟩

theorem ratF_injective : Function.Injective (ratF E n) := by
  haveI : Nontrivial (Af E) := nontrivial_finiteAdeles
  intro g h e
  apply Units.ext
  ext i j
  have := congrArg (fun x : GL (Fin n) (Af E) => x.val i j) e
  exact (algebraMap E (Af E)).injective this

theorem pFin_ratGL (g : GL (Fin n) E) : GeneralLinearGroup.map (pFin E) (ratGL E n g) = ratF E n g := by
  apply Units.ext
  ext i j
  rfl

theorem cV_ratGL (v : InfinitePlace E) (g : GL (Fin n) E) :
    GeneralLinearGroup.map (cV v) (ratGL E n g) = GeneralLinearGroup.map v.embedding g := by
  apply Units.ext
  ext i j
  exact pInf_algebraMap (g.val i j) v

theorem mem_twCent_iff {u : GL (Fin n) E} (hu : IsTransl u) (g d : GL (Fin n) E) :
    g ∈ PositivityTheory.Rg.Tf.Loc.twCent (thetaE E n) d ↔ g * (d * u⁻¹) = d * u⁻¹ * thE E n g := by
  rw [PositivityTheory.Rg.Tf.Loc.mem_twCent, hu.1 g]
  constructor
  · intro h
    have h' : g * d = d * thetaE E n g := by
      calc g * d = g * (g⁻¹ * d * thetaE E n g) := by rw [h]
        _ = d * thetaE E n g := by group
    calc g * (d * u⁻¹) = g * d * u⁻¹ := by group
      _ = d * thetaE E n g * u⁻¹ := by rw [h']
      _ = d * u⁻¹ * (u * thetaE E n g * u⁻¹) := by group
  · intro h
    have h' : g * d = d * thetaE E n g := by
      calc g * d = g * (d * u⁻¹) * u := by group
        _ = d * u⁻¹ * (u * thetaE E n g * u⁻¹) * u := by rw [h]
        _ = d * thetaE E n g := by group
    calc g⁻¹ * d * thetaE E n g = g⁻¹ * (d * thetaE E n g) := by group
      _ = g⁻¹ * (g * d) := by rw [h']
      _ = d := by group

theorem mem_twCent_iff_ratF {u : GL (Fin n) E} (hu : IsTransl u) (g d : GL (Fin n) E) :
    g ∈ PositivityTheory.Rg.Tf.Loc.twCent (thetaE E n) d ↔
      ratF E n g * ratF E n (d * u⁻¹) = ratF E n (d * u⁻¹) * thF E n (ratF E n g) := by
  rw [mem_twCent_iff hu, thF_ratF, ← map_mul, ← map_mul]
  exact ratF_injective.eq_iff.symm

theorem map_mem_twCent (v : InfinitePlace E) {g d : GL (Fin n) E}
    (h : g ∈ PositivityTheory.Rg.Tf.Loc.twCent (thetaE E n) d) :
    GeneralLinearGroup.map v.embedding g ∈
      PositivityTheory.Rg.Tf.Loc.twCent (thetaR (starRingEnd ℂ) n) (GeneralLinearGroup.map v.embedding d) := by
  have h' : g⁻¹ * d * thetaE E n g = d := h
  rw [PositivityTheory.Rg.Tf.Loc.mem_twCent]
  rw [← map_thetaR v.embedding (conjE E) (starRingEnd ℂ)
    (fun x => IsCMField.complexEmbedding_complexConj E v.embedding x) n g, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg _ h'

theorem centEq : CentEq := by
  intro E _ _ _ a b u₁ u₂ h₁ h₂ d₁ d₂
  refine ⟨fun y => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨⟨⟨g₁, g₂⟩, rfl⟩, hc⟩
    have hc' := Prod.ext_iff.1 hc
    refine ⟨(ratGL E a g₁, ratGL E b g₂), ?_, ?_⟩
    · exact ⟨⟨g₁, (mem_twCent_iff_ratF h₁ g₁ d₁).2 hc'.1, rfl⟩, ⟨g₂, (mem_twCent_iff_ratF h₂ g₂ d₂).2 hc'.2, rfl⟩⟩
    · exact Prod.ext (pFin_ratGL g₁) (pFin_ratGL g₂)
  · rintro ⟨⟨γ₁, γ₂⟩, ⟨⟨g₁, hg₁, rfl⟩, ⟨g₂, hg₂, rfl⟩⟩, rfl⟩
    have e : (comps (ratGL E a g₁, ratGL E b g₂)).2 = (ratF E a g₁, ratF E b g₂) :=
      Prod.ext (pFin_ratGL g₁) (pFin_ratGL g₂)
    rw [e]
    exact ⟨⟨(g₁, g₂), rfl⟩, Prod.ext ((mem_twCent_iff_ratF h₁ g₁ d₁).1 hg₁) ((mem_twCent_iff_ratF h₂ g₂ d₂).1 hg₂)⟩
  · rintro ⟨γ₁, γ₂⟩ ⟨⟨g₁, hg₁, rfl⟩, ⟨g₂, hg₂, rfl⟩⟩
    refine ⟨fun h => ?_, fun v => ?_⟩
    · have e : (comps (ratGL E a g₁, ratGL E b g₂)).2 = (ratF E a g₁, ratF E b g₂) :=
        Prod.ext (pFin_ratGL g₁) (pFin_ratGL g₂)
      rw [e] at h
      have e₁ : g₁ = 1 := ratF_injective ((congrArg Prod.fst h).trans (map_one _).symm)
      have e₂ : g₂ = 1 := ratF_injective ((congrArg Prod.snd h).trans (map_one _).symm)
      subst e₁ e₂
      exact Prod.ext (map_one _) (map_one _)
    · constructor
      · show GeneralLinearGroup.map (cV v) (ratGL E a g₁) ∈ _
        rw [cV_ratGL]
        exact map_mem_twCent v hg₁
      · show GeneralLinearGroup.map (cV v) (ratGL E b g₂) ∈ _
        rw [cV_ratGL]
        exact map_mem_twCent v hg₂

end GlobalTheory.CompanionTheory.TwistCent

end
end

section

noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.QConjug

variable {G : Type} [Group G]

def conjEquiv {H H' : Subgroup G} {g : G} (hH' : ∀ x, x ∈ H' ↔ g * x * g⁻¹ ∈ H) : H' ≃ H where
  toFun x := ⟨g * x * g⁻¹, (hH' x).1 x.2⟩
  invFun y := ⟨g⁻¹ * y * g, (hH' _).2 (by
    have : g * (g⁻¹ * (y : G) * g) * g⁻¹ = y := by group
    rw [this]; exact y.2)⟩
  left_inv x := Subtype.ext (by simp only []; group)
  right_inv y := Subtype.ext (by simp only []; group)

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableSingletonClass G]

theorem normaliser_conj {H H' : Subgroup G} {g : G} (hH' : ∀ x, x ∈ H' ↔ g * x * g⁻¹ ∈ H)
    {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H Measure.count ρ) :
    IsQuotNormaliser H' Measure.count (fun x => ρ (g * x)) := by
  unfold IsQuotNormaliser at hρ ⊢
  refine ⟨hρ.1.comp (measurable_const_mul g), fun y => ?_⟩
  have h1 := hρ.2 (g * y)
  rw [lintegral_count] at h1 ⊢
  rw [← h1, ← (conjEquiv hH').tsum_eq]
  refine tsum_congr fun x => ?_
  show ρ (g * ((x : G) * y)) = ρ (g * (x : G) * g⁻¹ * (g * y))
  congr 1
  group

theorem normaliser_unconj {H H' : Subgroup G} {g : G} (hH' : ∀ x, x ∈ H' ↔ g * x * g⁻¹ ∈ H)
    {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H' Measure.count ρ) :
    IsQuotNormaliser H Measure.count (fun x => ρ (g⁻¹ * x)) := by
  have h2 : ∀ x, x ∈ H ↔ g⁻¹ * x * g⁻¹⁻¹ ∈ H' := by
    intro x
    rw [hH', show g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x by group]
  exact normaliser_conj h2 hρ

theorem qConjOf_holds : QConjOf := by
  intro hI G _ _ _ _ _ μ _ _ H H' _ F g hF hFH hH'
  haveI : Countable H' := Countable.of_equiv _ (conjEquiv hH').symm
  by_cases hex : ∃ ρ, IsQuotNormaliser H Measure.count ρ
  · obtain ⟨ρ, hρ⟩ := hex
    have hρ' := normaliser_conj hH' hρ
    have hmeas : Measurable fun x => F (g * x) := hF.comp (measurable_const_mul g)
    have hinv : ∀ h ∈ H', ∀ x, F (g * (h * x)) = F (g * x) := by
      intro h hh x
      have := hFH (g * h * g⁻¹) ((hH' h).1 hh) (g * x)
      rw [← this]
      congr 1
      group
    rw [hI G μ H' (fun x => F (g * x)) (fun x => ρ (g * x)) hmeas hinv hρ',
      hI G μ H F ρ hF hFH hρ]
    exact integral_mul_left_eq_self (fun x => F x * ((ρ x).toReal : ℂ)) g
  · have hex' : ¬ ∃ ρ, IsQuotNormaliser H' Measure.count ρ := by
      rintro ⟨ρ, hρ⟩
      exact hex ⟨_, normaliser_unconj hH' hρ⟩
    unfold quotIntegral
    rw [dite_eq_right hex, dite_eq_right hex']

end GlobalTheory.CompanionTheory.QConjug

end
end

section

open Matrix
open PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (twConj)

namespace GlobalTheory.CompanionTheory.EllProp

theorem twConj_twConj {G : Type*} [Group G] (θ : Monoid.End G) (x g d : G) :
    twConj θ x (twConj θ g d) = twConj θ (g * x) d := by
  simp only [twConj, map_mul]
  group

theorem orbit_preimage_eq {G : Type*} [Group G] (θ : Monoid.End G) (g d : G) (C : Set G) :
    {x | twConj θ x (twConj θ g d) ∈ C} = (fun y => g⁻¹ * y) '' {y | twConj θ y d ∈ C} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, twConj_twConj]
  constructor
  · intro h
    exact ⟨g * x, h, by group⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem ellProperOf : EllProperOf := by
  intro hD hP _ n d hd C hC
  obtain ⟨g, d', z, h1, h2, h3, rfl⟩ := hD n d hd
  rw [orbit_preimage_eq]
  exact (hP n d' z h1 h2 h3 C hC).image (continuous_const.mul continuous_id)

end GlobalTheory.CompanionTheory.EllProp
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2

theorem _root_.GlobalTheory.T.character_weight_map : ChWMap := by
  first | exact @GlobalTheory.CompanionTheory.CharInf.chWMap | exact GlobalTheory.CompanionTheory.CharInf.chWMap | (intros; apply GlobalTheory.CompanionTheory.CharInf.chWMap <;> assumption)
end
