module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CongNum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.ZmPow
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle002

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w}

structure AwR (x y : WD h) : Prop where
  pol : ∀ g : ↥(Weil h), x.charPol g = y.charPol g
  n0 : y.mono0 → x = y

theorem AwR.of_eq {x y : WD h} (e : x = y) : AwR x y := ⟨fun _ => by rw [e], fun _ => e⟩

theorem AwR.eq_unr {x y : WD h} (k : AwR x y) (hy : y.unr) : x = y := k.n0 (WD.unr_mono0 _ hy)

def RatioW (x : WD h) : Prop :=
  ∀ φ : ↥(Weil h), deg φ = 1 → ∀ α ∈ x.eig φ, ∀ β ∈ x.eig φ, ‖α‖ < ((normV w : ℕ) : ℝ) * ‖β‖
end Local

section Real
variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ}

structure IsGalRU (π : TR.CuspSub F a) (ι : Qbar l ≃+* ℂ) (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin a) (Qbar l)) (wt : ℤ)
    (HT : (F →+* Qbar l) → Multiset ℤ) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  away : ∀ (w : HeightOneSpectrum (𝓞 F)) (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion F) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → AwR (wdOf h hl ι r) (rc (algNorm σ))
  ratio : ∀ (w : HeightOneSpectrum (𝓞 F)) (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion F) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → (rc (algNorm σ)).mono0 →
      RatioW (wdOf h hl ι r)
  weights : ∀ (τ : F →+* Qbar l) (m : Multiset ℂ), π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) m →
    (HT τ).map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z
  weights_sym : ∀ τ : F →+* Qbar l, HT τ = (HT τ).map (wt - ·)
  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (_root_.ReciprocityTheory.Gal.Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw),
      IsdRAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) ∧
      (∀ (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) τ (HT τ)) ∧
      (∀ σ, π.IsLocComp w σ → GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion F) (Fin a)) ≠ ⊥ →
        GlobalTheory.SmGL.IsSpherical σ.ρ → ∀ rc, IsRec h rc →
          (∀ g : ↥(Weil h), (wdAt P ι Bw h hj (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype)).charPol g = (rc (algNorm σ)).charPol g) ∧
          ((rc (algNorm σ)).mono0 → (wdAt P ι Bw h hj (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype)).mono0)) ∧
      ∀ σ, π.IsLocComp w σ → GlobalTheory.SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype)
end Real

def ExRN : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) [Fact (n = 2)], 1 ≤ n → ∀ (π : TR.CuspSub F n) (χ : HChar F), π.IsRegAlg → π.Polarized χ →
    ∃ (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)) (wt : ℤ) (HT : (F →+* Qbar l) → Multiset ℤ), IsGalRU π ι r wt HT ∧ AttR ι r π ∧
      ∀ r' : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l), Continuous r' → AttR ι r' π → IsGalRU π ι r' wt HT

end UpperTheory.GalN.V
end
end

section

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br

namespace UpperTheory.GalN.V.Win.N

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V.CongNum

section

private theorem normV_rat {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    normV w = p := by
  have h : normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hN : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
    simp
  have hd : Ideal.absNorm w.asIdeal ∣ p :=
    hN ▸ Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)
  rw [h]
  refine ((Nat.dvd_prime hp).1 hd).resolve_left ?_
  rw [Ideal.absNorm_eq_one_iff]
  exact w.isPrime.ne_top

private theorem est {p e : ℕ} (hp : 5 ≤ p) (he : 2 ≤ e) {t z₁ z₂ z₃ : ℂ} (h1 : ‖z₁‖ = 1) (h2 : ‖z₂‖ = 1) (h3 : ‖z₃‖ = 1)
    (ht : ‖t‖ ≤ 3 * (Real.sqrt p * (p : ℝ) ^ ((((e : ℤ) + 1 : ℤ) : ℝ) / 2)) + (p : ℝ) ^ ((((e : ℤ) + 1 : ℤ) : ℝ) / 2)) :
    t - eis4 p e z₁ z₂ z₃ ≠ 0 ∧ ‖t - eis4 p e z₁ z₂ z₃‖ ≤ (p : ℝ) ^ (2 * (e + 1)) := by
  have hp' : (5 : ℝ) ≤ p := by exact_mod_cast hp
  set x : ℝ := (p : ℝ) ^ ((((e : ℤ) + 1 : ℤ) : ℝ) / 2) with hx
  set y : ℝ := (p : ℝ) ^ e with hy
  have hx0 : 0 ≤ x := by positivity
  have hxx : x * x = p * y := by
    rw [hx, ← Real.rpow_add (by linarith), hy, ← pow_succ', ← Real.rpow_natCast]
    congr 1; push_cast; ring
  have hy2 : (p : ℝ) ^ 2 ≤ y := pow_le_pow_right₀ (by linarith) he
  have hy0 : 0 ≤ y := by positivity
  have hxy : 2 * x ≤ y := by
    refine abs_le_of_sq_le_sq' ?_ hy0 |>.2
    nlinarith [mul_le_mul_of_nonneg_right hy2 hy0, mul_nonneg (show (0:ℝ) ≤ p - 4 by linarith) (mul_nonneg (show (0:ℝ) ≤ p by linarith) hy0)]
  have hsx : Real.sqrt p * x ≤ y := by
    refine abs_le_of_sq_le_sq' ?_ hy0 |>.2
    rw [mul_pow, Real.sq_sqrt (by linarith), pow_two x, hxx]
    nlinarith [mul_le_mul_of_nonneg_right hy2 hy0]
  replace ht : ‖t‖ ≤ 7 / 2 * y := by linarith
  have n1 : ‖(p : ℂ) ^ (e + 1) * z₁‖ = p * y := by simp [h1, hy, pow_succ']
  have n2 : ‖(p : ℂ) ^ e * z₂‖ = y := by simp [h2, hy]
  have n3 : ‖(p : ℂ) * z₃‖ = p := by simp [h3]
  have hr : ‖t - ((p : ℂ) ^ e * z₂ + (p : ℂ) * z₃ + 1)‖ ≤ 7 / 2 * y + (y + p + 1) := by
    refine (norm_sub_le _ _).trans (add_le_add ht ?_)
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, ← n2, ← n3]
    have := norm_add_le ((p : ℂ) ^ e * z₂) ((p : ℂ) * z₃)
    simpa using this
  have hE : t - eis4 p e z₁ z₂ z₃ = (t - ((p : ℂ) ^ e * z₂ + (p : ℂ) * z₃ + 1)) - (p : ℂ) ^ (e + 1) * z₁ := by
    rw [eis4]; ring
  have hlt : 7 / 2 * y + (y + p + 1) < p * y := by nlinarith
  constructor
  · intro h0
    rw [hE, sub_eq_zero] at h0
    rw [h0, n1] at hr
    linarith
  · rw [hE]
    refine (norm_sub_le _ _).trans ?_
    rw [n1, mul_comm 2, pow_mul, pow_succ' (p : ℝ) e, ← hy]
    have : (2 : ℝ) ≤ p * y := by nlinarith
    nlinarith

private theorem size {c A M e N d p : ℕ} (hN : N ≤ c * (M * (e + 1 + 1)) ^ A) (hM : 1 ≤ M) (hp : 5 ≤ p) :
    ((N * d : ℕ) : ℝ) * Real.log ((p : ℝ) ^ (2 * (e + 1))) ≤
      ((c * 2 ^ A * 2 : ℕ) : ℝ) * d * ((M : ℝ) * (e + 1)) ^ (A + 1) * Real.log p := by
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have h1 : N * d * (2 * (e + 1)) ≤ c * 2 ^ A * 2 * d * (M * (e + 1)) ^ (A + 1) := by
    have a1 : (M * (e + 1 + 1)) ^ A ≤ 2 ^ A * (M * (e + 1)) ^ A := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by nlinarith) _
    have a2 : e + 1 ≤ M * (e + 1) := Nat.le_mul_of_pos_left _ hM
    calc N * d * (2 * (e + 1)) ≤ c * (2 ^ A * (M * (e + 1)) ^ A) * d * (2 * (M * (e + 1))) := by
          gcongr
          exact hN.trans (by gcongr)
      _ = _ := by ring
  rw [Real.log_pow, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hl
  exact_mod_cast h1

end

end

end UpperTheory.GalN.V.Win.N
end

section

open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Hi

section
variable {H Y Z : Type} {I : Type 1} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]

private theorem span_push (σ : I → SmIrr H) (π : Representation ℂ H Y) (ρ : Representation ℂ H Z)
    (p : Y →ₗ[ℂ] Z) (hp : Function.Surjective p) (he : ∀ g v, p (π g v) = ρ g (p v))
    (hs : ∀ y, y ∈ ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Y // ∀ g v, f ((σ i).ρ g v) = π g (f v)}), LinearMap.range f.1) :
    ∀ z, z ∈ ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Z // ∀ g v, f ((σ i).ρ g v) = ρ g (f v)}), LinearMap.range f.1 := by
  intro z
  obtain ⟨y, rfl⟩ := hp z
  have hle : (⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Y // ∀ g v, f ((σ i).ρ g v) = π g (f v)}), LinearMap.range f.1) ≤
      (⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Z // ∀ g v, f ((σ i).ρ g v) = ρ g (f v)}), LinearMap.range f.1).comap p := by
    refine iSup_le fun i => iSup_le fun f => ?_
    rintro _ ⟨v, rfl⟩
    have h : LinearMap.range (p ∘ₗ f.1) ≤
        ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Z // ∀ g v, f ((σ i).ρ g v) = ρ g (f v)}), LinearMap.range f.1 :=
      le_iSup_of_le i (le_iSup_of_le
        (⟨p ∘ₗ f.1, fun g v => by simp only [LinearMap.comp_apply]; rw [f.2 g v, he]⟩ :
          {f : (σ i).V →ₗ[ℂ] Z // ∀ g v, f ((σ i).ρ g v) = ρ g (f v)}) le_rfl)
    exact h ⟨v, rfl⟩
  exact hle (hs y)

private theorem iso_push (τ : SmIrr H) (π : Representation ℂ H Y) (ρ : Representation ℂ H Z)
    (p : Y →ₗ[ℂ] Z) (hp : Function.Surjective p) (he : ∀ g v, p (π g v) = ρ g (p v))
    (h : IsoSum π ⊤ τ) : IsoSum ρ ⊤ τ := by
  intro z _
  obtain ⟨y, rfl⟩ := hp z
  have hle : (⨆ f : {f : τ.V →ₗ[ℂ] Y // (∀ g v, f (τ.ρ g v) = π g (f v)) ∧ LinearMap.range f ≤ ⊤}, LinearMap.range f.1) ≤
      (⨆ f : {f : τ.V →ₗ[ℂ] Z // (∀ g v, f (τ.ρ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ ⊤}, LinearMap.range f.1).comap p := by
    refine iSup_le fun f => ?_
    rintro _ ⟨v, rfl⟩
    have h' : LinearMap.range (p ∘ₗ f.1) ≤
        ⨆ f : {f : τ.V →ₗ[ℂ] Z // (∀ g v, f (τ.ρ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ ⊤}, LinearMap.range f.1 :=
      le_iSup_of_le
        (⟨p ∘ₗ f.1, fun g v => by simp only [LinearMap.comp_apply]; rw [f.2.1 g v, he], le_top⟩ :
          {f : τ.V →ₗ[ℂ] Z // (∀ g v, f (τ.ρ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ ⊤}) le_rfl
    exact h' ⟨v, rfl⟩
  exact hle (h Submodule.mem_top)

private theorem iso_quot (σ : I → SmIrr H) (π : Representation ℂ H Y) (ρ : Representation ℂ H Z)
    (p : Y →ₗ[ℂ] Z) (hp : Function.Surjective p) (he : ∀ g v, p (π g v) = ρ g (p v))
    (hs : ∀ y, y ∈ ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Y // ∀ g v, f ((σ i).ρ g v) = π g (f v)}), LinearMap.range f.1)
    (i₀ : I)
    (hk : (⨆ (i : {i : I // IsEmpty ((σ i₀).ρ.Equiv (σ i).ρ)})
      (f : {f : (σ i.1).V →ₗ[ℂ] Y // ∀ g v, f ((σ i.1).ρ g v) = π g (f v)}), LinearMap.range f.1) ≤ LinearMap.ker p) :
    IsoSum ρ ⊤ (σ i₀) := by
  intro z _
  obtain ⟨y, rfl⟩ := hp z
  have hle : (⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Y // ∀ g v, f ((σ i).ρ g v) = π g (f v)}), LinearMap.range f.1) ≤
      (⨆ f : {f : (σ i₀).V →ₗ[ℂ] Z // (∀ g v, f ((σ i₀).ρ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ ⊤}, LinearMap.range f.1).comap p := by
    refine iSup_le fun i => iSup_le fun f => ?_
    rintro _ ⟨v, rfl⟩
    by_cases hi : IsEmpty ((σ i₀).ρ.Equiv (σ i).ρ)
    · have h0 : f.1 v ∈ LinearMap.ker p :=
        hk (Submodule.mem_iSup_of_mem ⟨i, hi⟩ (Submodule.mem_iSup_of_mem ⟨f.1, f.2⟩ ⟨v, rfl⟩))
      rw [Submodule.mem_comap, LinearMap.mem_ker.1 h0]
      exact Submodule.zero_mem _
    · obtain ⟨e⟩ := not_isEmpty_iff.1 hi
      have h' : LinearMap.range (p ∘ₗ f.1 ∘ₗ e.toLinearEquiv.toLinearMap) ≤
          ⨆ f : {f : (σ i₀).V →ₗ[ℂ] Z // (∀ g v, f ((σ i₀).ρ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ ⊤}, LinearMap.range f.1 :=
        le_iSup_of_le
          (⟨p ∘ₗ f.1 ∘ₗ e.toLinearEquiv.toLinearMap, fun g v => by
            have h1 := (congrArg f.1 (e.toIntertwiningMap.isIntertwining _ _ g v)).trans (f.2 g _)
            exact (congrArg p h1).trans (he g _), le_top⟩ :
            {f : (σ i₀).V →ₗ[ℂ] Z // (∀ g v, f ((σ i₀).ρ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ ⊤}) le_rfl
      refine h' ⟨e.toLinearEquiv.symm v, ?_⟩
      exact congrArg (fun w => p (f.1 w)) (e.toLinearEquiv.apply_symm_apply v)
  exact hle (hs y)

end

private theorem stab_N {Q : Type} [Finite Q] [DecidableEq Q] {H : Q → Type} [∀ q, Group (H q)]
    {Y : Type} {I : Type 1} [AddCommGroup Y] [Module ℂ Y] (q : Q) (V : I → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (τ : ∀ i, Representation ℂ (H q) (V i))
    (π : Representation ℂ (∀ q, H q) Y) (P : I → Prop) (g : ∀ q, H q) :
    (⨆ (i : {i : I // P i}) (f : {f : V i.1 →ₗ[ℂ] Y // ∀ h v, f (τ i.1 h v) = π (Pi.mulSingle q h) (f v)}),
      LinearMap.range f.1) ≤
    (⨆ (i : {i : I // P i}) (f : {f : V i.1 →ₗ[ℂ] Y // ∀ h v, f (τ i.1 h v) = π (Pi.mulSingle q h) (f v)}),
      LinearMap.range f.1).comap (π g) := by
  set N : Submodule ℂ Y := ⨆ (i : {i : I // P i})
    (f : {f : V i.1 →ₗ[ℂ] Y // ∀ h v, f (τ i.1 h v) = π (Pi.mulSingle q h) (f v)}), LinearMap.range f.1 with hN
  let S : Submonoid (∀ q, H q) :=
    { carrier := {g | N ≤ N.comap (π g)}
      one_mem' := fun n hn => by simpa using hn
      mul_mem' := fun {a b} ha hb n hn => by
        have : π (a * b) n = π a (π b n) := by rw [map_mul]; rfl
        rw [Submodule.mem_comap, this]
        exact ha (hb hn) }
  refine Submonoid.pi_mem_of_mulSingle_mem (H := S) g fun q' => ?_
  show N ≤ N.comap (π (Pi.mulSingle q' (g q')))
  refine iSup_le fun i => iSup_le fun f => ?_
  rintro _ ⟨v, rfl⟩
  by_cases hq : q' = q
  · subst hq
    rw [Submodule.mem_comap, ← f.2 (g q') v]
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem f ⟨_, rfl⟩)
  · have hc : ∀ (h : H q) (x : Y), π (Pi.mulSingle q' (g q')) (π (Pi.mulSingle q h) x) =
        π (Pi.mulSingle q h) (π (Pi.mulSingle q' (g q')) x) := fun h x => by
      have h1 : π (Pi.mulSingle q' (g q') * Pi.mulSingle q h) x = π (Pi.mulSingle q h * Pi.mulSingle q' (g q')) x := by
        rw [(Pi.mulSingle_commute hq (g q') h).eq]
      rw [map_mul, map_mul] at h1
      exact h1
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem
      ⟨π (Pi.mulSingle q' (g q')) ∘ₗ f.1, fun h w => by
        simp only [LinearMap.comp_apply]
        rw [f.2 h w, hc]⟩ ⟨v, rfl⟩)

theorem UpperTheory.GalN.V.isoRefine :
        (∀ (H Y : Type) (I : Type 1) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup Y] [Module ℂ Y] (σ : I → SmIrr H) (π : Representation ℂ H Y), (∀ y, y ∈ ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Y // ∀ g v, f ((σ i).ρ g v) = π g (f v)}), LinearMap.range f.1) → ∀ y : Y, y ≠ 0 → ∃ i₀ : I, y ∉ ⨆ (i : {i : I // IsEmpty ((σ i₀).ρ.Equiv (σ i).ρ)}) (f : {f : (σ i.1).V →ₗ[ℂ] Y // ∀ g v, f ((σ i.1).ρ g v) = π g (f v)}), LinearMap.range f.1) → ∀ (Q : Type) [Finite Q] [DecidableEq Q] (H : Q → Type) [∀ q, Group (H q)] [∀ q, TopologicalSpace (H q)] [∀ q, IsTopologicalGroup (H q)] (Y : Type) (I : Type 1) [AddCommGroup Y] [Module ℂ Y] (σ : I → ∀ q, SmIrr (H q)) (π : Representation ℂ (∀ q, H q) Y), (∀ q y, y ∈ ⨆ (i : I) (f : {f : (σ i q).V →ₗ[ℂ] Y // ∀ g v, f ((σ i q).ρ g v) = π (Pi.mulSingle q g) (f v)}), LinearMap.range f.1) → ∀ y : Y, y ≠ 0 → ∃ (Y' : Type) (_ : AddCommGroup Y') (_ : Module ℂ Y') (π' : Representation ℂ (∀ q, H q) Y') (p : Y →ₗ[ℂ] Y') (c : Q → I), p y ≠ 0 ∧ (∀ g v, p (π g v) = π' g (p v)) ∧ ∀ q, IsoSum (π'.comp (MonoidHom.mulSingle H q)) ⊤ (σ (c q) q) := by
  intro hPick Q _ _ H _ _ _ Y I _ _ σ π hs y hy
  haveI := Fintype.ofFinite Q
  have key : ∀ T : Finset Q, ∃ (Y' : Type) (_ : AddCommGroup Y') (_ : Module ℂ Y')
      (π' : Representation ℂ (∀ q, H q) Y') (p : Y →ₗ[ℂ] Y') (c : Q → I),
      Function.Surjective p ∧ p y ≠ 0 ∧ (∀ g v, p (π g v) = π' g (p v)) ∧
      (∀ q ∈ T, IsoSum (π'.comp (MonoidHom.mulSingle H q)) ⊤ (σ (c q) q)) ∧
      (∀ q y, y ∈ ⨆ (i : I) (f : {f : (σ i q).V →ₗ[ℂ] Y' // ∀ g v, f ((σ i q).ρ g v) = π' (Pi.mulSingle q g) (f v)}), LinearMap.range f.1) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      exact ⟨Y, _, _, π, LinearMap.id,
        fun q => (hPick (H q) Y I (fun i => σ i q) (π.comp (MonoidHom.mulSingle H q)) (hs q) y hy).choose,
        Function.surjective_id, hy, fun _ _ => rfl, by simp, hs⟩
    | insert q T hq ih =>
      obtain ⟨Y', _, _, π', p, c, hsurj, hpy, he, hiso, hsp⟩ := ih
      obtain ⟨i₀, hi₀⟩ := hPick (H q) Y' I (fun i => σ i q) (π'.comp (MonoidHom.mulSingle H q)) (hsp q) (p y) hpy
      set N : Submodule ℂ Y' := ⨆ (i : {i : I // IsEmpty ((σ i₀ q).ρ.Equiv (σ i q).ρ)})
        (f : {f : (σ i.1 q).V →ₗ[ℂ] Y' // ∀ g v, f ((σ i.1 q).ρ g v) = π' (Pi.mulSingle q g) (f v)}),
        LinearMap.range f.1 with hNdef
      have hi₀' : p y ∉ N := hi₀
      have hN : ∀ g, N ≤ N.comap (π' g) := fun g =>
        stab_N q (fun i => (σ i q).V) (fun i => (σ i q).ρ) π' (fun i => IsEmpty ((σ i₀ q).ρ.Equiv (σ i q).ρ)) g
      have hmk : ∀ g v, N.mkQ (π' g v) = π'.quotient N hN g (N.mkQ v) := fun g v => rfl
      refine ⟨Y' ⧸ N, inferInstance, inferInstance, π'.quotient N hN, N.mkQ ∘ₗ p, Function.update c q i₀,
        (N.mkQ_surjective).comp hsurj, ?_, ?_, ?_, ?_⟩
      · simpa using hi₀'
      · intro g v
        simp only [LinearMap.comp_apply]
        rw [he, hmk]
      · intro q' hq'
        rcases Finset.mem_insert.1 hq' with rfl | hq'
        · rw [Function.update_self]
          exact iso_quot (fun i => σ i q') (π'.comp (MonoidHom.mulSingle H q'))
            ((π'.quotient N hN).comp (MonoidHom.mulSingle H q')) N.mkQ N.mkQ_surjective
            (fun g v => hmk _ v) (hsp q') i₀ (by rw [Submodule.ker_mkQ]; exact le_rfl)
        · have hne : q' ≠ q := fun h => hq (h ▸ hq')
          rw [Function.update_of_ne hne]
          exact iso_push _ (π'.comp (MonoidHom.mulSingle H q'))
            ((π'.quotient N hN).comp (MonoidHom.mulSingle H q')) N.mkQ N.mkQ_surjective
            (fun g v => hmk _ v) (hiso q' hq')
      · intro q'
        exact span_push (fun i => σ i q') (π'.comp (MonoidHom.mulSingle H q'))
          ((π'.quotient N hN).comp (MonoidHom.mulSingle H q')) N.mkQ N.mkQ_surjective
          (fun g v => hmk _ v) (hsp q')
  obtain ⟨Y', i1, i2, π', p, c, -, hpy, he, hiso, -⟩ := key Finset.univ
  exact ⟨Y', i1, i2, π', p, c, hpy, he, fun q => hiso q (Finset.mem_univ q)⟩
end

section

open UpperTheory.GalN.V

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

end SlopeTestRemainingChoices

end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem span_of_equiv {K K' H n : Type} [CommRing K] [CommRing K'] [Fintype n] [DecidableEq n] (e : K ≃+* K')
    (f : H → Matrix n n K) (f' : H → Matrix n n K') (hf : ∀ g i j, f' g i j = e (f g i j))
    (h : Submodule.span K' (Set.range f') = ⊤) : Submodule.span K (Set.range f) = ⊤ := by
  have key : ∀ x ∈ Submodule.span K' (Set.range f'), x.map e.symm ∈ Submodule.span K (Set.range f) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨g, rfl⟩ := ha
      refine Submodule.subset_span ⟨g, ?_⟩
      ext i j
      simp [hf]
    | zero =>
      have : (0 : Matrix n n K').map e.symm = 0 := by ext i j; simp
      rw [this]; exact zero_mem _
    | add a b _ _ ha hb =>
      have : (a + b).map e.symm = a.map e.symm + b.map e.symm := by ext i j; simp
      rw [this]; exact add_mem ha hb
    | smul s a _ ha =>
      have : (s • a).map e.symm = e.symm s • a.map e.symm := by ext i j; simp
      rw [this]; exact Submodule.smul_mem _ _ ha
  rw [eq_top_iff]
  intro y _
  have h1 := key (y.map e) (by rw [h]; trivial)
  have h2 : (y.map e).map e.symm = y := by ext i j; simp
  rwa [h2] at h1

private theorem charpoly_mapRep {R R' H : Type} [CommRing R] [CommRing R'] [Group H] (f : R →+* R') (r r' : H →* M4 R)
    (h : ∀ g, (r g).charpoly = (r' g).charpoly) (g : H) : (mapRep f r g).charpoly = (mapRep f r' g).charpoly := by
  change ((r g).map f).charpoly = ((r' g).map f).charpoly
  rw [Matrix.charpoly_map, Matrix.charpoly_map, h]

end
end
