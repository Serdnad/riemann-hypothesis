module

public import Formalism.HermitianCurvature.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle092
public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle067
public import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.PeriodIntegrals.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle098
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle010
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle082
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle087
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.LocalToGlobal.Divisibility.Numbers

@[expose] public section

section

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory

theorem starProjection_splitCasimirStd_last : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → (Module.End.eigenspace Om (β + L l + 0)).starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wP L M l : ℂ) • v := by
  intro V _ _ _ n E Et Om β L l hH hadj hEt hOm M v hv
  have hq : ∀ w v, qdet E w v = (∏ j, (w + shf β L j)) • v := hH.cap
  obtain ⟨K, hK, hK'⟩ := comatrix_last_row_inverts_casimir V n E Om (shf β L) hH.gl hq hOm
  obtain ⟨-, -, hsym, -⟩ := tensorStd_rel_adjoint_splitCasimir V n E Et Om hH.gl hadj hEt hOm
  have hev := splitCasimirStd_eigenvalue V n E Et Om (shf β L) hH.gl hadj hq hEt hOm
  have hinj : Function.Injective (shf β L) := by
    intro a b h
    apply hH.anti.injective
    have h' : (L a : ℂ) = (L b : ℂ) := add_left_cancel h
    exact_mod_cast h'
  have hcont : Continuous fun u : ℂ => cpol (shf β M) (u - 1) := by
    unfold cpol
    fun_prop
  have h := ev_starProjection_eigenspace_eq_residue (PiLp 2 (fun _ : Fin (n + 1) => V)) V (n + 1)
    (shf β L) 0 Om (PiLp.projₗ 2 (fun _ : Fin (n + 1) => V) (Fin.last n)) K
    (fun u : ℂ => cpol (shf β M) (u - 1)) (PiLp.single 2 (Fin.last n) v) v l hinj hsym hev hK hcont
    (fun u => (hK' u v).trans (mem_CapSp.1 hv (u - 1)))
  refine Eq.trans h ?_
  congr 1
  simp only [cpol, shf, WigSh.wP]
  push_cast
  congr 1
  · exact Finset.prod_congr rfl fun j _ => by ring
  · exact Finset.prod_congr rfl fun j _ => by ring

end GlobalTheory
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.PlaceClosedField

theorem vLa_pos_of_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
    {x : 𝓞 K} (hx : x ∈ la.asIdeal) (h0 : x ≠ 0) : 0 < vLa la ((x : 𝓞 K) : K) := by
  have h1 : la.intValuation x < 1 := (la.intValuation_lt_one_iff_mem _).2 hx
  have h2 : WithZero.log (la.intValuation x) < 0 := by
    have := (WithZero.log_lt_log (la.intValuation_ne_zero _ h0) one_ne_zero).2 h1
    simpa using this
  have h : ((x : 𝓞 K) : K) = algebraMap (𝓞 K) K x := rfl
  rw [vLa, h, HeightOneSpectrum.valuation_of_algebraMap]
  omega

theorem ramOverZ_pos {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    0 < ramOverZ la := by
  have h := Crude.crv_vLa_char la
  have h0 : ((resCharOf la : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast (Crude.resCharOf_prime la).ne_zero
  have h1 := vLa_pos_of_mem la (Crude.crv_char_mem la) h0
  have h2 : ((((resCharOf la : ℕ) : 𝓞 K)) : K) = ((resCharOf la : ℕ) : K) := map_natCast (algebraMap (𝓞 K) K) _
  rw [h2, h] at h1
  exact_mod_cast h1

theorem vV_unit (T : CDVR) {x : T.V} (hx : IsUnit x) : vV T.V (algebraMap T.V T.Fr x) = 0 := by
  have h : valV T.V (algebraMap T.V T.Fr x) = 1 := by
    unfold valV
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    intro hm
    exact (IsLocalRing.mem_maximalIdeal _).1 hm hx
  simp [vV, h]

theorem le_nval_mul (T : CDVR) {e r : ℕ} (hr : 0 < r) (ν : ℝ) (x : T.Fr)
    (h : (((r : ℝ) * ν : ℝ) : EReal) ≤ nval T.V e x) : (ν : EReal) ≤ nval T.V (e * r) x := by
  by_cases hx : x = 0
  · subst hx; rw [nval_zero]; exact le_top
  rw [nval_of_ne hx, EReal.coe_le_coe_iff] at h ⊢
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rw [Nat.cast_mul, ← div_div, le_div_iff₀ hr', mul_comm]
  exact h

theorem exists_closed_field_over_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∃ (C : Type) (_ : Field C) (_ : CharZero C) (V : VF C) (ι : T.Fr →+* C), V.l = resCharOf la ∧ EmbOK T V ι ∧ IsAlgClosed C ∧ (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) ∧ (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) ∧ (∀ m : ℕ, ¬ resCharOf la ∣ m → V.v (m : C) = 0) ∧ ∀ (y : IntFr Xo c T io) (C3 : IntChart T io y) (k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ν : ℝ), (((ramOverZ la : ℝ) * ν : ℝ) : EReal) ≤ nuLocC C3 e k a n → (ν : EReal) ≤ nuLocC C3 (eOf T V) k a n := by
  intro E _ _ _ H Dw lv Xo c _ la T io e ho
  have hp := Crude.resCharOf_prime la
  have hr := ramOverZ_pos la
  have he : 0 < e := ho.1
  have hv : vV T.V ((resCharOf la : ℕ) : T.Fr) = (e : ℤ) * (ramOverZ la : ℤ) := by
    rw [← map_natCast io, ho.2, Crude.crv_vLa_char]
  have hpos : (0 : ℤ) < (e : ℤ) * (ramOverZ la : ℤ) := by positivity
  have hnu : ¬ IsUnit ((resCharOf la : ℕ) : T.V) := by
    intro hu
    have h0 := vV_unit T hu
    rw [map_natCast, hv] at h0
    omega
  obtain ⟨C, _, _, v, ι, h1, h2, h3, h4⟩ :=
    GlobalTheory.DvrClosedEmbedding.exists_complete_isAlgClosed_addValuation T _ hp hnu
  refine ⟨C, inferInstance, inferInstance, ⟨v, resCharOf la, hp, h1⟩, ι, rfl, h2, h3, h4, ?_, ?_, ?_⟩
  · intro x hx
    show (0 : WithTop ℝ) < v _
    by_cases h0 : x = 0
    · subst h0; simp
    have hx0 : ((x : 𝓞 c.F) : c.F) ≠ 0 := by simpa using h0
    rw [h2 _ ((map_ne_zero io).2 hx0), ho.2, hv]
    have := vLa_pos_of_mem la hx h0
    have h5 : (0 : ℝ) < (((e : ℤ) * vLa la ((x : 𝓞 c.F) : c.F) : ℤ) : ℝ) / (((e : ℤ) * (ramOverZ la : ℤ) : ℤ) : ℝ) := by
      apply div_pos
      · exact_mod_cast mul_pos (by exact_mod_cast he) this
      · exact_mod_cast hpos
    exact_mod_cast h5
  · intro m hm
    have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero _)
    have hm1 : ((m : ℕ) : c.F) ≠ 0 := by exact_mod_cast hm0
    show v (m : C) = 0
    rw [← map_natCast ι, ← map_natCast io, h2 _ ((map_ne_zero io).2 hm1), ho.2, Crude.crv_vLa_coprime la hm]
    simp
  · intro y C3 k a n ν h
    have hE : eOf T (⟨v, resCharOf la, hp, h1⟩ : VF C) = e * ramOverZ la := by
      show (vV T.V ((resCharOf la : ℕ) : T.Fr)).toNat = _
      rw [hv, ← Nat.cast_mul, Int.toNat_natCast]
    rw [hE]
    unfold nuLocC at h ⊢
    simp only [le_iInf_iff] at h ⊢
    intro P hP f hf
    exact le_nval_mul T hr ν _ (h P hP f hf)

end GlobalTheory.PlaceClosedField
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_conj_levelMap_by_levelMoves : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.EtaOK → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ρ₂ : d.Xo₂.X ≅ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂.hom) (gM gA gM₂ gA₂ : Dw.La →ₗ[𝓞 E] Dw.La), IsLevMove ρ ν gM gA → IsLevMove ρ₂.hom ν₂ gM₂ gA₂ → (∀ a, gM₂ a - gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ a, Dw.ModN l.A (gA₂ a - gA a)) → ∃ (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), ρ₂.hom ≫ r' = d.r ≫ ρ ∧ ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ ∧ DeltaDat.EtaOK { d with r := r', m := m' } := by
  first | exact @GlobalTheory.exists_conj_levelMap | exact GlobalTheory.exists_conj_levelMap | (intros; apply GlobalTheory.exists_conj_levelMap <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem quot_integral_rmul_of_measurable (hQ : PI.QuotInv) {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)}
    {μG μS ν : Measure (PI.MtM m)} (h : PI.QuotientSetting G S μG μS ν) (F : PI.MtM m → ℂ) (hF : Measurable F)
    (hinv : ∀ s ∈ S, ∀ x : PI.MtM m, Matrix.of x ∈ G → F (fun i j => (s * Matrix.of x) i j) = F x)
    {g : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ G) :
    ∫ x, F (fun i j => (Matrix.of x * g) i j) ∂ν = ∫ x, F x ∂ν := by
  have hc : Continuous (fun x : PI.MtM m => (fun i j => (Matrix.of x * g) i j : PI.MtM m)) := by
    have h1 : Continuous (fun x : PI.MtM m => (Matrix.of x : Matrix (Fin m) (Fin m) ℂ)) := continuous_id
    exact h1.matrix_mul continuous_const
  have hF' : Measurable (fun x : PI.MtM m => F (fun i j => (Matrix.of x * g) i j)) := hF.comp hc.measurable
  have hmap : ν.map (fun x : PI.MtM m => F (fun i j => (Matrix.of x * g) i j)) = ν.map F := by
    ext A hA
    rw [Measure.map_apply hF' hA, Measure.map_apply hF hA, ← lintegral_indicator_one (hF' hA),
      ← lintegral_indicator_one (hF hA)]
    have key := hQ m G S μG μS ν h (fun x => A.indicator (1 : ℂ → ℝ≥0∞) (F x))
      ((measurable_one.indicator hA).comp hF) (fun s hs x hx => by simp only [hinv s hs x hx]) g hg
    exact key
  have e1 := integral_map (μ := ν) hF'.aemeasurable (f := fun y : ℂ => y) aestronglyMeasurable_id
  have e2 := integral_map (μ := ν) hF.aemeasurable (f := fun y : ℂ => y) aestronglyMeasurable_id
  rw [← e1, ← e2, hmap]

theorem quot_integral_rmul : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (F : Mx k r → ℂ), SideG k r z π u μW μN μG νq → ContinuousOn F (GG k r) → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x ∈ GG k r, F (s * x) = F x) → Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) νq → ∀ g ∈ GG k r, ∫ x, F ((Matrix.of x) * g) ∂νq = ∫ x, F (Matrix.of x) ∂νq := by
  classical
  intro k r Wp _ _ _ _ z π u μW μN μG νq F hS hF hinv _ g hg
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨hGG, hGH⟩ := GlobalTheory.T.isMatGroup_GG_and_haar_right_invariant k r
  obtain ⟨hGH1, hGH2⟩ := hGH μG hG
  obtain ⟨hSG, hsub, hS1, hS2⟩ := GlobalTheory.T.besselSubgroup_product_measure_isHaar k r z μW μN hz hT hW hN
  have hset : PI.QuotientSetting (GG k r) (Formalism.QuantumDeterminants.Sset k r z) μG (muSof μW μN) νq :=
    ⟨hGG, hSG, hsub, hGH1, hS1, hGH2, hS2, hq⟩
  obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
  set A : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ GG k r} with hA
  have hAm : MeasurableSet A := by
    have := (Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet (k := k) (r := r)).compl
    convert this using 1
    ext x
    simp [hA]
  have hc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) A := hF
  have hm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0)) :=
    hc.measurable_piecewise continuousOn_const hAm
  have hval : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ GG k r →
      A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0) x = F (Matrix.of x) :=
    fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have key := quot_integral_rmul_of_measurable GlobalTheory.T.quotientMeasure_right_invariant hset _ hm (fun s hs x hx => by
    rw [hval x hx]
    exact (hval (fun i j => (s * Matrix.of x) i j) (hGG.2.2.1 s (hsub hs) _ hx)).trans (hinv s hs _ hx)) hg
  calc ∫ x, F ((Matrix.of x) * g) ∂νq
      = ∫ x, A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0)
          (fun i j => (Matrix.of x * g) i j) ∂νq := by
        refine integral_congr_ae (hae.mono fun x hx => ?_)
        exact (hval (fun i j => (Matrix.of x * g) i j) (hGG.2.2.1 _ hx g hg)).symm
    _ = ∫ x, A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0) x ∂νq := key
    _ = ∫ x, F (Matrix.of x) ∂νq := integral_congr_ae (hae.mono fun x hx => hval x hx)

end GlobalTheory
end
