module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle020
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LocalConditionsWeightedConditional
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle223
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle360
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle355
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016

@[expose] public section

section

open GlobalTheory.KZ GlobalTheory.Ord2 UpperTheory.V.HV Formalism.ConjugateSelfDual PowerSeries

noncomputable section

namespace GlobalTheory.KZ.AutoPin

variable {l : ℕ} [Fact l.Prime]

def compPow (l : ℕ) [Fact l.Prime] (B : PowerSeries (Qbar l)) : PowerSeries (Qbar l) :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), B.coeff k * ((((Polynomial.X + 1) ^ l - 1 : Polynomial (Qbar l))) ^ k).coeff n

theorem norm_l_lt_one : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [map_natCast] at h
  rw [h, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem norm_l_pos : 0 < ‖((l : ℕ) : Qbar l)‖ := by
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [map_natCast] at h
  rw [h, Padic.norm_p]
  exact inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)

theorem norm_lpow_anti {k n : ℕ} (h : k ≤ n) : ‖((l : ℕ) : Qbar l) ^ n‖ ≤ ‖((l : ℕ) : Qbar l) ^ k‖ := by
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) norm_l_lt_one.le h

theorem cg_trans {n : ℕ} {a b d : Qbar l} (h1 : Cg n a b) (h2 : Cg n b d) : Cg n a d := by
  unfold Cg at *
  calc ‖a - d‖ = ‖(a - b) + (b - d)‖ := by ring_nf
    _ ≤ max ‖a - b‖ ‖b - d‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ _ := max_le h1 h2

theorem cg_mono {k n : ℕ} {a b : Qbar l} (h : Cg n a b) (hk : k ≤ n) : Cg k a b :=
  le_trans h (norm_lpow_anti hk)

theorem cg_mul {n : ℕ} {x a b : Qbar l} (hx : ‖x‖ ≤ 1) (h : Cg n a b) : Cg n (x * a) (x * b) := by
  unfold Cg at *
  rw [← mul_sub, norm_mul]
  exact le_trans (mul_le_of_le_one_left (norm_nonneg _) hx) h

theorem norm_tval_le (B : PowerSeries (Qbar l)) (N : ℕ) (z : Qbar l) (hB : ∀ n, ‖B.coeff n‖ ≤ 1) (hz : ‖z - 1‖ ≤ 1) :
    ‖tval B N z‖ ≤ 1 := by
  unfold tval
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun n _ => ?_
  rw [norm_mul, norm_pow]
  exact mul_le_one₀ (hB n) (by positivity) (pow_le_one₀ (norm_nonneg _) hz)

theorem tval_sub (P Q : PowerSeries (Qbar l)) (N : ℕ) (z : Qbar l) : tval (P - Q) N z = tval P N z - tval Q N z := by
  unfold tval; rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun n _ => ?_; simp [sub_mul]

theorem tval_smul (x : Qbar l) (P : PowerSeries (Qbar l)) (N : ℕ) (z : Qbar l) : tval (x • P) N z = x * tval P N z := by
  unfold tval; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => ?_; simp [mul_assoc]

theorem isIntegral_iff_norm_le_one (x : Qbar l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  (isIntegral_iff_norm_le_one x).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

theorem intCast_mem (c : Coef l) (n : ℤ) : ((n : ℤ) : Qbar l) ∈ c.O := by
  have : ((n : ℤ) : Qbar l) = algebraMap ℤ_[l] (Qbar l) (n : ℤ_[l]) := by simp
  rw [this]; exact c.O.algebraMap_mem _

theorem polyPow_coeff_int (k n : ℕ) : ∃ t : ℤ,
    ((((Polynomial.X + 1) ^ l - 1 : Polynomial (Qbar l))) ^ k).coeff n = (t : Qbar l) := by
  refine ⟨((((Polynomial.X + 1) ^ l - 1 : Polynomial ℤ)) ^ k).coeff n, ?_⟩
  have : (((Polynomial.X + 1) ^ l - 1 : Polynomial (Qbar l))) ^ k =
      Polynomial.map (Int.castRingHom (Qbar l)) ((((Polynomial.X + 1) ^ l - 1 : Polynomial ℤ)) ^ k) := by
    simp [Polynomial.map_pow, Polynomial.map_sub]
  rw [this, Polynomial.coeff_map]; rfl

theorem compPow_coeff_mem (c : Coef l) (B : PowerSeries (Qbar l)) (hB : ∀ n, B.coeff n ∈ c.O) (n : ℕ) :
    (compPow l B).coeff n ∈ c.O := by
  unfold compPow
  rw [PowerSeries.coeff_mk]
  refine sum_mem fun k _ => mul_mem (hB k) ?_
  obtain ⟨t, ht⟩ := polyPow_coeff_int (l := l) k n
  rw [ht]; exact intCast_mem c t

end GlobalTheory.KZ.AutoPin
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TraceClassRank

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FormTies GlobalTheory.OnTies
open Formalism.HermitianLatticesTheory (localization₂)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 2000] Submodule.module

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Trace

variable {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (ι : Fin D.R.m)
  (ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l))
  (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ)

def traceLat : Submodule (𝓞 D.what₂.LL) (Fin (R.nW ι) → D.what₂.LL) :=
  Submodule.span (𝓞 D.what₂.LL)
    ((fun f : U → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) =>
        ∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo h fw ι (f u)) ''
      {f | IsOrbitFamily (T.Q.Xo ((ι : ℕ) + 1)) T.Q.c (badN D) (wtA (κ ι)) (T.dδ ((ι : ℕ) + 1) (κ ι).n) (fun u : U => ℓ u)
        fun u => ((f u).1 : T.R ((ι : ℕ) + 1))})

def CompareAt (lam : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  localization₂ lam.asIdeal (traceLat h fw ι ℓ U ψ) ≤ localization₂ lam.asIdeal (thetaBase R ι U ψ ph v p)

def CompareOffOwn : Prop := ∀ lam, Formalism.EigenvalueLevelCeiling.plc lam ≠ p → CompareAt h fw ι ℓ U ψ ph v p lam

variable {h fw ι ℓ U ψ ph v p} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
    {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
    {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
    {O : OnObj S P oc} {i : Bs.J}
    {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
      D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
    {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
    {inc : P →* G}
    {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A ι (R.mu v) U ψ) → D.what₂.LL)}

def comapEquiv {P G : Type} [Group P] [Group G] {inc : P →* G} (hi : Function.Injective inc) {U : Subgroup G}
    (hU : U ≤ inc.range) : U.comap inc ≃ U :=
  Equiv.ofBijective (fun u => ⟨inc u, u.2⟩) ⟨fun _ _ e => Subtype.ext (hi (congrArg Subtype.val e)), fun u => by
    obtain ⟨g, hg⟩ := hU u.2
    exact ⟨⟨g, show inc g ∈ U from hg ▸ u.2⟩, Subtype.ext hg⟩⟩

theorem isOrbitFamily_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {bad : ℕ} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {d : DeltaDat Xo c n} {I I' : Type}
    {m : I → (LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l)} {m' : I' → (LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l)}
    {f : I → Rul Xo c} (hf : IsOrbitFamily Xo c bad a d m f) (e : I' → I) (he : ∀ u, m' u = m (e u)) :
    IsOrbitFamily Xo c bad a d m' fun u => f (e u) := by
  obtain ⟨Λ, N, x₀, P, x, h1, h2, h3, h4, h5, h6, h7⟩ := hf
  exact ⟨Λ, N, x₀, P, fun u => x (e u), h1, h2, h3, h4, h5, h6, fun u => he u ▸ h7 (e u)⟩

theorem Th0_eq_comap (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (hi : Function.Injective inc)
    (hU : U ≤ inc.range) :
    O.Th0 v i = (traceLat h fw ι ℓ U ψ).comap ((toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)) := by
  have hm : (O.Th0 v i).map ((toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)) = traceLat h fw ι ℓ U ψ := by
    rw [t.Th0_eq, t.U_eq]
    unfold thetaEig traceSpan traceLat
    rw [Submodule.map_span, Set.image_image]
    have key : ∀ f : U → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι),
        (toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)
          (∑ᶠ u : U.comap inc, O.ψ (u : P) • z.symm (1 ⊗ₜ[(recB h.toLawsCore).KO] f (comapEquiv hi hU u))) =
        ∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo h fw ι (f u) := fun f => by
      rw [map_finsum _ (Set.toFinite _), ← finsum_comp_equiv (comapEquiv hi hU)]
      refine finsum_congr fun u => ?_
      rw [map_smul, LinearMap.restrictScalars_apply, toForms_tmul, one_smul, ← algebraMap_smul D.what₂.LL]
      exact congrArg (· • _) (t.ψ_eq u u.2)
    congr 1
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      refine ⟨fun u => f ((comapEquiv hi hU).symm u), isOrbitFamily_comp hf _ (fun u => ?_), ?_⟩
      · exact congrArg (fun a : U => ℓ a) ((comapEquiv hi hU).apply_symm_apply u).symm
      · refine (key _).symm.trans ?_
        simp only [Equiv.symm_apply_apply]
    · rintro ⟨f, hf, rfl⟩
      exact ⟨fun u => f (comapEquiv hi hU u), isOrbitFamily_comp hf _ fun u => rfl, key f⟩
  rw [← hm]
  exact (Submodule.comap_map_eq_of_injective (f := (toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL))
    (toForms_bijective h fw ι z).1 _).symm

theorem trace_lattice_le_theta_lattice_at_place (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (hi : Function.Injective inc)
    (hU : U ≤ inc.range) {n : ℕ} (hp : RunPin R ι n v p) (hA : CompareOffOwn h fw ι ℓ U ψ ph v p) :
    localization₂ v.asIdeal (O.Th0 v i) ≤ localization₂ v.asIdeal (O.ThJ v i) := by
  rw [Th0_eq_comap t hi hU, t.ThJ_eq]
  refine localization_comap_le v _ (hA v fun e => ?_)
  have h1 := hp.1
  split_ifs at h1 with h2
  · exact D.host.pde_ne (h2.symm.trans (e.trans h1))
  · exact h2 (e.trans h1)

end Trace

section Place

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type}
  [Group P] [Finite P] {c : OnConst}

def RankAtPlaces (O : OnObj S P c) : Prop :=
  AtPair S fun v => ∀ j, Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) ((O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K))) ∧
    Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) (O.eJ v j) ∧ localization₂ v.asIdeal (O.Th0 v j) ≤ localization₂ v.asIdeal (O.ThJ v j)

def fillJ (O : OnObj S P c) : OnObj S P c := { O with ThJ := fun v j => O.ThJ v j ⊔ O.Th0 v j }

theorem leafRankJ_fillJ {O : OnObj S P c} (h : RankAtPlaces O) : LeafRankJ (fillJ O) := by
  have key : ∀ v j, Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) ((O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K))) →
      Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) (O.eJ v j) → Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) ((fillJ O).eJ v j) := fun v j a b => by
    change Formalism.EigenvalueLevelCeiling.IsLatIn _ ((O.ThJ v j ⊔ O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K)))
    rw [Submodule.map_sup]
    refine ⟨b.1.sup a.1, le_antisymm (Submodule.span_le.2 ?_) ?_⟩
    · change _ ≤ (O.Zg j).restrictScalars (𝓞 K)
      exact sup_le (fun x hx => b.2.le (Submodule.subset_span hx)) fun x hx => a.2.le (Submodule.subset_span hx)
    · exact b.2.ge.trans (Submodule.span_mono (show O.eJ v j ≤ _ from le_sup_left))
  exact fun w hw =>
    ⟨fun j => ⟨((h w hw).1 j).1, key _ j ((h w hw).1 j).1 ((h w hw).1 j).2.1, le_sup_right⟩,
      fun j => ⟨((h w hw).2 j).1, key _ j ((h w hw).2 j).1 ((h w hw).2 j).2.1, le_sup_right⟩⟩

theorem lix_fillJ {O : OnObj S P c} {v : HeightOneSpectrum (𝓞 K)} {j : Bs.J}
    (h : localization₂ v.asIdeal (O.Th0 v j) ≤ localization₂ v.asIdeal (O.ThJ v j)) (M : Submodule (𝓞 K) (Fin (O.nZ j) → K)) :
    Formalism.EigenvalueLevelCeiling.lix v M ((fillJ O).eJ v j) = Formalism.EigenvalueLevelCeiling.lix v M (O.eJ v j) := by
  have h1 : O.ThJ v j ⊔ O.Th0 v j ≤ localization₂ v.asIdeal (O.ThJ v j) :=
    sup_le (Formalism.HermitianLatticesTheory.locBasic_le_locS _ _) ((Formalism.HermitianLatticesTheory.locBasic_le_locS _ _).trans h)
  have h2 : (fillJ O).eJ v j ≤ localization₂ v.asIdeal (O.eJ v j) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hsx⟩ := h1 hx
    exact ⟨s, hs, _, hsx, map_smul ((O.e j).restrictScalars (𝓞 K)) s x⟩
  have h3 : localization₂ v.asIdeal ((fillJ O).eJ v j) = localization₂ v.asIdeal (O.eJ v j) :=
    le_antisymm ((Formalism.HermitianLatticesTheory.locBasic_locS_mono _ h2).trans (Formalism.HermitianLatticesTheory.locBasic_locS_idem _ _).le)
      (Formalism.HermitianLatticesTheory.locBasic_locS_mono _ (Submodule.map_mono le_sup_left))
  exact (Formalism.EigenvalueLevelCeiling.lix_locP v M _).trans ((congrArg _ h3).trans (Formalism.EigenvalueLevelCeiling.lix_locP v M _).symm)

theorem leafTW1_fillJ {O : OnObj S P c} (h : RankAtPlaces O) (h1 : LeafTW1 O) : LeafTW1 (fillJ O) :=
  ⟨fun w hw =>
    ⟨fun j => ⟨((h1.1 w hw).1 j).1, ((h1.1 w hw).1 j).2.trans_eq
        (congrArg (fun a : ℤ => (a : ℝ) + _) (lix_fillJ ((h w hw).1 j).2.2 _).symm)⟩,
      fun j => ⟨((h1.1 w hw).2 j).1, ((h1.1 w hw).2 j).2.trans_eq
        (congrArg (fun a : ℤ => (a : ℝ) + _) (lix_fillJ ((h w hw).2 j).2.2 _).symm)⟩⟩, h1.2⟩

theorem on_core_atPlaces (N : IndefNum Bs) (O : OnObj S P c) (CE : ℝ) (hRk : RankRows S)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : LatticeIndexBoundAtPairs O) (hD : LeafData O) (hJ : RankAtPlaces O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : LeafTW1 O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood N O) (hR : LeafDepthRam N O) (h2p : LeafDepth2 N O) (hL : LeafDepthLevel N O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hJS : LeafJSum O) (hJE : LeafJExp N O) (hCE : c.CE ≤ CE) (tE1 : ErrorConstantMatchesDefinition N O CE) : ONwith S N O.errOn :=
  on_core N (fillJ O) CE hRk hMk hSup hProj hC hSp hS hT0 hD (leafRankJ_fillJ hJ) hI h2 (leafTW1_fillJ hJ h1) hSh hIU hBS hUn
    hG hR h2p hL hPg hSz hX hBad hJS hJE hCE tE1

end Place

section Row

variable {T : HeightOneSpectrum (𝓞 D.what₂.LL) → Full D} [inst : ∀ v, Algebra (T v).J.Q.c.F D.what₂.LL]
  {R : ∀ v, RealDat D A (T v).J.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ v (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), ((R v).MW i σ).Vec}
  {h : ∀ v, LawsP (T v).toTop} {fw : ∀ v, FWTie (T v).J (R v) κ (v₀ v)} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
  {p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {ι : Bs.J → Fin D.R.m} {wL wF : ∀ i, WeightFamilies.Wt D ((ι i : ℕ) + 1)} {nT : ℕ}
  {z : ∀ v i, (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB (h v).toLawsCore).KO] (recB (h v).toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i))}
  {act : ∀ v i, P → (recB (h v).toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i)) →
    (recB (h v).toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i))}
  {inc : P →* G}
  {ℓ : ∀ v i, G → (LaMod ((T v).Q.Dw ((ι i : ℕ) + 1)) (T v).Q.l ≃ₗ[𝓞 D.host.E] LaMod ((T v).Q.Dw ((ι i : ℕ) + 1)) (T v).Q.l)}
  {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : HeightOneSpectrum (𝓞 D.what₂.LL) → Bs.J → ℂ}
  {y : ∀ v i, (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A (ι i) ((R v).mu v) U ψ) → D.what₂.LL)}

end Row

end GlobalTheory.TraceClassRank
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Sl2Ad

theorem form_isSymm {K : Type} [Field K] : (form (K := K)).IsSymm := by
  first
  | exact ⟨fun v w => by simp only [RingHom.id_apply, form_apply]; ring⟩
  | exact fun v w => by simp only [RingHom.id_apply, form_apply]; ring
  | (intro v w; simp only [RingHom.id_apply, form_apply]; ring)

theorem form_ad {K : Type} [Field K] (A : GL (Fin 2) K) (v w : Fin 3 → K) :
    form (ad A *ᵥ v) (ad A *ᵥ w) = form v w := by
  rw [← coord_conj_ofCoord, ← coord_conj_ofCoord,
    form_coord (by rw [trace_conj, trace_ofCoord]) (by rw [trace_conj, trace_ofCoord])]
  conv_rhs => rw [← coord_ofCoord v, ← coord_ofCoord w, form_coord (trace_ofCoord v) (trace_ofCoord w)]
  have : ((A : Matrix (Fin 2) (Fin 2) K) * ofCoord v * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
      ((A : Matrix (Fin 2) (Fin 2) K) * ofCoord w * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
      = (A : Matrix (Fin 2) (Fin 2) K) * (ofCoord v * ofCoord w) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    have h : ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), h, Matrix.one_mul]
  rw [this, trace_conj]

theorem form_nondegenerate {K : Type} [Field K] [CharZero K] : (form (K := K)).Nondegenerate := by
  rw [form, LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero]
  simp [Matrix.det_fin_three]

theorem coord_smul_scalar {F K : Type} [Field F] [Field K] [Algebra F K] (a : F) (X : Matrix (Fin 2) (Fin 2) K) :
    coord (a • X) = a • coord X := by
  ext i; fin_cases i <;> simp [coord]

theorem coord_sum {K : Type} [Field K] {ι : Type} (s : Finset ι) (f : ι → Matrix (Fin 2) (Fin 2) K) :
    coord (∑ i ∈ s, f i) = ∑ i ∈ s, coord (f i) := by
  ext j; fin_cases j <;> simp [coord, Matrix.sum_apply]

end GlobalTheory.Sl2Ad


open GlobalTheory.Sl2Ad in
theorem GlobalTheory.Sl2Ad.augmentation_contains_one : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] (r : Γ →* GL (Fin 2) (Qbar l)), (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → IsIrr r → ∃ (n : ℕ) (γ : Fin n → Γ) (a : Fin n → ℚ_[l]), ∀ X : Matrix (Fin 2) (Fin 2) (Qbar l), X.trace = 0 → X = ∑ i, a i • ((r (γ i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * ((r (γ i))⁻¹ : GL (Fin 2) (Qbar l)) - X) := by
  intro l _ c Γ _ r _ hirr
  set S : Γ →* Matrix (Fin 3) (Fin 3) (Qbar l) := adHom.comp r with hS
  have hSg : ∀ g, S g = ad (r g) := fun g => rfl
  have h1 := GlobalTheory.T.one_mem_span_sub_one_of_orthogonal_irreducible_three S form form_nondegenerate form_isSymm (fun g v w => form_ad _ v w)
    (fun v hv => GlobalTheory.T.forall_ad_invariant_eq_zero_of_isIrr r hirr v (fun g => by rw [← hSg]; exact hv g))
    (fun y hy hy' => GlobalTheory.T.traceForm_ne_zero_of_stable_line_irreducible r hirr y hy (fun g => by rw [← hSg]; exact hy' g))
  obtain ⟨n, b, g, hg⟩ := Submodule.mem_span_set'.mp h1
  choose γ hγ using fun i => (g i).2
  have hdet : (∑ i, b i • (S (γ i) - 1)).det ≠ 0 := by
    have : ∑ i, b i • (S (γ i) - 1) = 1 :=
      (Finset.sum_congr rfl fun i _ => by rw [← hγ i]).trans hg
    rw [this, Matrix.det_one]; exact one_ne_zero
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_nat_coeffs_det_sum_smul_ne_zero (fun i => S (γ i) - 1) b hdet
  set J : Submodule ℚ_[l] (Matrix (Fin 3) (Fin 3) (Qbar l)) := Submodule.span ℚ_[l] (Set.range fun g => S g - 1) with hJ
  have hmul : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨h, rfl⟩ := hy
        have : (S g - 1) * (S h - 1) = (S (g * h) - 1) - (S g - 1) - (S h - 1) := by
          rw [map_mul]; noncomm_ring
        rw [this]
        exact J.sub_mem (J.sub_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)) (Submodule.subset_span ⟨_, rfl⟩)
      | zero => rw [mul_zero]; exact J.zero_mem
      | add y z _ _ hy hz => rw [mul_add]; exact J.add_mem hy hz
      | smul t y _ hy => rw [mul_smul_comm]; exact J.smul_mem t hy
    | zero => rw [zero_mul]; exact J.zero_mem
    | add x z _ _ hx hz => rw [add_mul]; exact J.add_mem hx hz
    | smul t x _ hx => rw [smul_mul_assoc]; exact J.smul_mem t hx
  have hT : (∑ i, (a i : Qbar l) • (S (γ i) - 1)) ∈ J := by
    refine J.sum_mem fun i _ => ?_
    rw [Nat.cast_smul_eq_nsmul]
    exact J.nsmul_mem (Submodule.subset_span ⟨_, rfl⟩) _
  have hone := GlobalTheory.T.one_mem_of_mul_mem_of_det_ne_zero J hmul _ hT ha
  obtain ⟨n', a', g', hg'⟩ := Submodule.mem_span_set'.mp hone
  choose γ' hγ' using fun i => (g' i).2
  refine ⟨n', γ', a', fun X hX => ?_⟩
  have htr : (∑ i, a' i • ((r (γ' i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * ((r (γ' i))⁻¹ : GL (Fin 2) (Qbar l)) - X)).trace = 0 := by
    rw [Matrix.trace_sum]; refine Finset.sum_eq_zero fun i _ => ?_
    rw [Matrix.trace_smul, Matrix.trace_sub, trace_conj, hX, sub_zero, smul_zero]
  refine ((ofCoord_coord hX).symm.trans ?_).trans (ofCoord_coord htr)
  congr 1
  rw [coord_sum]
  have : ∀ i, coord (a' i • ((r (γ' i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * (((r (γ' i))⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) - X))
      = (a' i • (S (γ' i) - 1)) *ᵥ coord X := by
    intro i
    rw [coord_smul_scalar, show ((r (γ' i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * (((r (γ' i))⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) - X)
      = (r (γ' i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * (((r (γ' i))⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) + (-1 : Qbar l) • X by
        rw [neg_one_smul, ← sub_eq_add_neg], coord_add, coord_conj _ hX, coord_smul, hSg, Matrix.smul_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec, neg_one_smul, ← sub_eq_add_neg]
  simp_rw [this, ← Matrix.sum_mulVec]
  have e : ∑ i, a' i • (S (γ' i) - 1) = 1 :=
    (Finset.sum_congr rfl fun i _ => by rw [← hγ' i]).trans hg'
  rw [e, Matrix.one_mulVec]
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem resRep_contAction : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl) (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1), Continuous W → ContAction (resRep c W hO S hN) := by
  intro l _ Ω _ _ S W c hO hN hW

  have hred : ∀ m : ResPlane c, Continuous fun s : G ℚ Ω => resAct c W hO s m := by
    intro m
    rw [continuous_iff_continuousAt]
    intro s
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [locConst_mod_pow l Ω c W hW hO 1 s] with t ht
    have hw : wRed c W t = wRed c W s := by
      ext i j
      obtain ⟨o, ho, e⟩ := ht i j
      have hd : mat W t i j - mat W s i j ∈ c.O := c.O.sub_mem (hO t i j) (hO s i j)
      have h0 : redL c (mat W t i j - mat W s i j) = 0 :=
        (redL_eq_zero_iff c hd).2 ⟨o, ho, by rw [e, pow_one]⟩
      rw [redL_sub c (hO t i j) (hO s i j)] at h0
      exact sub_eq_zero.1 h0
    rw [resAct_apply, resAct_apply, hw]
  have hq : ∀ m : ResPlane c, Continuous fun g : GS Ω (S : Set Pl) => resRep c W hO S hN g m := by
    intro m
    rw [(QuotientGroup.isQuotientMap_mk (NS Ω (S : Set Pl))).continuous_iff]
    exact hred m
  show Continuous fun p : GS Ω (S : Set Pl) × ResPlane c => (resRep c W hO S hN p.1) p.2
  exact continuous_prod_of_discrete_right.2 hq

end GlobalTheory.Ord2
end
