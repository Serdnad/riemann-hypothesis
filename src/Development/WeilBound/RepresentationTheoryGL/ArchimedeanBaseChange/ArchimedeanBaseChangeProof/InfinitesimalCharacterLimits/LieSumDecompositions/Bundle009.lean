module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle259
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle240
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

section Quot

variable {M : Type} [AddCommGroup M] [Module ℂ M] (V I : Submodule ℂ M)

def Pa : Subalgebra ℂ (Module.End ℂ M) where
  carrier := {T | (∀ v ∈ V, T v ∈ V) ∧ ∀ v ∈ I, T v ∈ I}
  mul_mem' := fun {_ _} hS hT => ⟨fun v hv => hS.1 _ (hT.1 v hv), fun v hv => hS.2 _ (hT.2 v hv)⟩
  add_mem' := fun {_ _} hS hT => ⟨fun v hv => V.add_mem (hS.1 v hv) (hT.1 v hv), fun v hv => I.add_mem (hS.2 v hv) (hT.2 v hv)⟩
  algebraMap_mem' := fun c => ⟨fun _ hv => V.smul_mem c hv, fun _ hv => I.smul_mem c hv⟩

def piQ : Pa V I →ₐ[ℂ] Module.End ℂ (V ⧸ I.comap V.subtype) where
  toFun T := (I.comap V.subtype).mapQ (I.comap V.subtype) (T.1.restrict T.2.1) (fun v hv => T.2.2 _ hv)
  map_one' := by
    ext v
    rfl
  map_mul' S T := by
    ext v
    rfl
  map_zero' := by
    ext v
    rfl
  map_add' S T := by
    ext v
    rfl
  commutes' c := by
    ext v
    rfl

theorem piQ_eq_zero {T : Pa V I} (h : piQ V I T = 0) : ∀ v ∈ V, T.1 v ∈ I := by
  intro v hv
  have e := LinearMap.congr_fun h (Submodule.Quotient.mk ⟨v, hv⟩)
  rw [LinearMap.zero_apply] at e
  change Submodule.Quotient.mk (T.1.restrict T.2.1 ⟨v, hv⟩) = 0 at e
  rw [Submodule.Quotient.mk_eq_zero] at e
  exact e

theorem piQ_eq_algebraMap {T : Pa V I} (c : ℂ) (h : ∀ v ∈ V, T.1 v - c • v ∈ I) : piQ V I T = algebraMap ℂ _ c := by
  ext v
  change Submodule.Quotient.mk (T.1.restrict T.2.1 v) = Submodule.Quotient.mk (c • v)
  rw [Submodule.Quotient.eq]
  exact h v.1 v.2

end Quot

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def Sl (N : ℕ) : Subalgebra ℂ (Module.End ℂ (Sm E N)) := Algebra.adjoin ℂ (Set.range (lie E N))

theorem lie_mem_Sl {N : ℕ} (X : Lie E N) : lie E N X ∈ Sl (E := E) N := Algebra.subset_adjoin ⟨X, rfl⟩

theorem Eop_mem_Sl {N : ℕ} (τ : E →+* ℂ) (i j : Fin N) : Eop τ i j ∈ Sl (E := E) N := by
  have h1 : lieS E N i j (atEmb τ 1) ∈ Sl (E := E) N := by rw [lieS_apply]; exact lie_mem_Sl _
  have h2 : lieS E N i j (atEmb τ Complex.I) ∈ Sl (E := E) N := by rw [lieS_apply]; exact lie_mem_Sl _
  have e : Eop τ i j = (1 / 2 : ℂ) • (lieS E N i j (atEmb τ 1) - Complex.I • lieS E N i j (atEmb τ Complex.I)) := rfl
  rw [e]
  exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ h1 (Subalgebra.smul_mem _ h2 _)) _

theorem qdet_mem {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) {n : ℕ} (X : Fin n → Fin n → A)
    (hX : ∀ i j, X i j ∈ S) (u : ℂ) : Formalism.REAL.qdet X u ∈ S := by
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hX _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

theorem Sl_comm_cap {N : ℕ} (τ : E →+* ℂ) (u : ℂ) {T : Module.End ℂ (Sm E N)} (hT : T ∈ Sl N) :
    Commute (cap τ u) T := by
  have hle : Sl (E := E) N ≤ Subalgebra.centralizer ℂ {cap (a := N) τ u} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨X, rfl⟩
    refine (Subalgebra.mem_centralizer_iff ℂ).2 ?_
    rintro y rfl
    exact (GlobalTheory.SpehInfChar.cap_commute_act τ u (.lie X)).eq
  exact (Subalgebra.mem_centralizer_iff ℂ).1 (hle hT) _ rfl

theorem Sl_comm_ltr {N : ℕ} (h : GA E N) {T : Module.End ℂ (Sm E N)} (hT : T ∈ Sl N) :
    Commute (JFinTr.ltr h) T := by
  have hle : Sl (E := E) N ≤ Subalgebra.centralizer ℂ {JFinTr.ltr h} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨X, rfl⟩
    refine (Subalgebra.mem_centralizer_iff ℂ).2 ?_
    rintro y rfl
    exact (JFinTr.ltr_lie h X).eq
  exact (Subalgebra.mem_centralizer_iff ℂ).1 (hle hT) _ rfl

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.PExpFin

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockExponential

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

def tl (r : ℕ) (s : ℝ) : Module.End ℂ (GA E N → ℂ) where
  toFun f g := f (aT E N r s * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tl_pow (r : ℕ) (s : ℝ) (i : ℕ) (f : GA E N → ℂ) : (tl r s ^ i) f = fun g => f (aT E N r (s * i) * g) := by
  induction i generalizing f with
  | zero =>
    funext g
    simp [aT_zero]
  | succ i ih =>
    funext g
    rw [pow_succ, Module.End.mul_apply, ih]
    show f (aT E N r s * (aT E N r (s * i) * g)) = f (aT E N r (s * ((i + 1 : ℕ) : ℝ)) * g)
    rw [← mul_assoc, ← aT_add, show s + s * (i : ℝ) = s * ((i + 1 : ℕ) : ℝ) by push_cast; ring]

theorem kl_iff (r : ℕ) (s : ℝ) (p : ℂ[X]) (F : GA E N → ℂ) : Kl r s p F ↔ aeval (tl r s) p F = 0 := by
  have e : aeval (tl (N := N) r s) p F = fun g => ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * F (aT E N r (s * j) * g) := by
    rw [aeval_eq_sum_range, LinearMap.sum_apply]
    funext g
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.smul_apply, tl_pow]
    rfl
  rw [e]
  constructor
  · intro h
    funext g
    exact h g
  · intro h g
    exact congrFun h g

theorem kl_mul {r : ℕ} {s : ℝ} {p q : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s p F) : Kl r s (p * q) F := by
  rw [kl_iff] at h ⊢
  rw [mul_comm, aeval_mul, Module.End.mul_apply, h, map_zero]

theorem kl_mul' {r : ℕ} {s : ℝ} {p q : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s q F) : Kl r s (p * q) F := by
  rw [mul_comm]
  exact kl_mul h

theorem ctn_eq_ct (r : ℕ) :
    letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
    ∃ μ : Measure (BlockIx N r → Ad E), μ.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratN E N r) (GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r) μ ∧
      ∀ f : Sm E N, An.ctn r f.1 = PositivityTheory.Affgl.CT.ct μ (GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r) f.1 := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, hμ, hD, hint⟩ := JDict.exists_normed E N r
  refine ⟨μ, hμ, hD, fun f => funext fun g => ?_⟩
  show An.ctn r f.1 g = ∫ x in GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r, f.1 (unip x * g) ∂μ
  rw [hint]
  simp only [An.ctn, GroundTheory.Automorphic.AutomorphicForm.constantTerm, GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip]

theorem ctn_add (r : ℕ) {φ ψ : Sm E N} (hφ : IsAutForm φ) (hψ : IsAutForm ψ) :
    An.ctn r (φ + ψ).1 = An.ctn r φ.1 + An.ctn r ψ.1 := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, hμ, hD, e⟩ := ctn_eq_ct (E := E) (N := N) r
  have := hμ
  rw [e, e, e]
  exact ct_add μ _ hD hφ hψ

theorem ctn_smul (r : ℕ) (c : ℂ) (φ : Sm E N) : An.ctn r (c • φ).1 = c • An.ctn r φ.1 := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  obtain ⟨μ, -, -, e⟩ := ctn_eq_ct (E := E) (N := N) r
  rw [e, e]
  exact ct_smul μ _ c φ

def Good (β : ℕ → ℝ) (φ : Sm E N) : Prop :=
  IsAutForm φ ∧ ∀ r, 0 < r → r < N → ∃ p : ℂ[X], p.Monic ∧ Kl r 1 p (An.ctn r φ.1) ∧ ∀ z, p.IsRoot z → ‖z‖ ≤ Real.exp (β r)

theorem good_bound {β : ℕ → ℝ} {φ : Sm E N} (h : Good β φ) :
    ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re ≤ β r := by
  intro r hr hrN c hc
  obtain ⟨p, -, hk, hroot⟩ := h.2 r hr hrN
  obtain ⟨F₀, hCT, F, hFspan, hF0, hFe⟩ := hc
  obtain ⟨-, -, -, hD⟩ := dict_holds E N
  obtain ⟨c₁, -, e₁⟩ := (hD φ h.1 r hr hrN).2 F₀ hCT
  have hk₀ : Kl r 1 p F₀ := by
    have : F₀ = c₁ • An.ctn r φ.1 := by
      funext g
      rw [e₁]
      rfl
    rw [this]
    exact (klSub r 1 p).smul_mem c₁ hk
  have hroot' := kl_eigen (kl_span hk₀ hFspan) hF0 hFe
  have h1 := hroot (Complex.exp (c * ((1 : ℝ) : ℂ))) hroot'
  rw [Complex.norm_exp] at h1
  have h2 := Real.exp_le_exp.1 h1
  simpa using h2

theorem good_of (β : ℕ → ℝ) {φ : Sm E N} (hφ : IsAutForm φ)
    (hexp : ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re ≤ β r) : Good β φ := by
  refine ⟨hφ, fun r hr hrN => ?_⟩
  obtain ⟨hA, -, -, hCT⟩ := dict_holds E N
  have hct := (hCT φ hφ r hr hrN).1
  have hfin := finTr_holds E N φ hφ r hr hrN _ hct
  have hadd : ∀ s t, aT E N r (s + t) = aT E N r s * aT E N r t := fun s t => aT_add r s t
  have hcont : ∀ g, Continuous fun t => An.ctn r φ.1 (aT E N r t * g) := by
    intro g
    have e : (fun t => An.ctn r φ.1 (aT E N r t * g)) = fun t => An.ctn r φ.1 (An.aR E N r t * g) :=
      funext fun t => by rw [hA]
    rw [e]
    exact JSqIntGlue.continuous_ctn_comp (GlobalTheory.CompanionTheory.ContAutForm.continuous_of_isAutForm_totallyComplex E N φ hφ) r
      ((JSqIntGlue.continuous_aR r).mul continuous_const)
  obtain ⟨p, hp, hpk, hroots⟩ := killPoly_holds (GA E N) (aT E N r) (An.ctn r φ.1) hadd hcont hfin
  refine ⟨p, hp, fun g => ?_, fun z hz => ?_⟩
  · have := hpk g
    simpa only [one_mul] using this
  · obtain ⟨c, rfl, F, hF, hF0, hFe⟩ := hroots z hz
    have hc : c ∈ Exp r φ.1 := ⟨_, hct, F, hF, hF0, hFe⟩
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (hexp r hr hrN c hc)

theorem good_add {β : ℕ → ℝ} {φ ψ : Sm E N} (hφ : Good β φ) (hψ : Good β ψ) : Good β (φ + ψ) := by
  refine ⟨GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_add hφ.1 hψ.1, fun r hr hrN => ?_⟩
  obtain ⟨p, hp, hpk, hpr⟩ := hφ.2 r hr hrN
  obtain ⟨q, hq, hqk, hqr⟩ := hψ.2 r hr hrN
  refine ⟨p * q, hp.mul hq, ?_, fun z hz => ?_⟩
  · rw [ctn_add r hφ.1 hψ.1]
    exact (klSub r 1 (p * q)).add_mem (kl_mul hpk) (kl_mul' hqk)
  · rcases (Polynomial.root_mul.1 hz) with h | h
    · exact hpr z h
    · exact hqr z h

theorem good_smul {β : ℕ → ℝ} {φ : Sm E N} (hφ : Good β φ) (c : ℂ) : Good β (c • φ) := by
  refine ⟨GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_smul c hφ.1, fun r hr hrN => ?_⟩
  obtain ⟨p, hp, hpk, hpr⟩ := hφ.2 r hr hrN
  refine ⟨p, hp, ?_, hpr⟩
  rw [ctn_smul]
  exact (klSub r 1 p).smul_mem c hpk

theorem good_zero (β : ℕ → ℝ) : Good β (0 : Sm E N) := by
  refine ⟨GlobalTheory.HCF.FormsSub.isAutForm_zero, fun r hr hrN => ⟨1, monic_one, ?_, fun z hz => ?_⟩⟩
  · have e : An.ctn r (0 : Sm E N).1 = (0 : ℂ) • An.ctn r (0 : Sm E N).1 := by
      rw [← ctn_smul, zero_smul]
    rw [e]
    exact (klSub r 1 1).smul_mem 0 (by
      intro g
      simp [An.ctn, GroundTheory.Automorphic.AutomorphicForm.constantTerm])
  · exact absurd hz (by simp [Polynomial.IsRoot])

theorem exp_span (S : Set (Sm E N)) (β : ℕ → ℝ) (haut : ∀ φ ∈ S, IsAutForm φ)
    (hexp : ∀ φ ∈ S, ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re ≤ β r) :
    ∀ φ ∈ Submodule.span ℂ S, ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re ≤ β r := by
  intro φ hφ
  refine good_bound ?_
  induction hφ using Submodule.span_induction with
  | mem x hx => exact good_of β (haut x hx) (hexp x hx)
  | zero => exact good_zero β
  | add x y _ _ hx hy => exact good_add hx hy
  | smul c x _ hx => exact good_smul hx c

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockExponential

end
end
