module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksCapA
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle208
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSum

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

def IsAutSt {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (U : Submodule ℂ (Sm E N)) : Prop :=
  _root_.GlobalTheory.CuspRep.IsStable U ∧ ∀ φ ∈ U, IsAutForm φ

def FinGen {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (U : Submodule ℂ (Sm E N)) : Prop :=
  ∃ S : Finset (Sm E N), (↑S : Set (Sm E N)) ⊆ U ∧ ∀ W : Submodule ℂ (Sm E N), _root_.GlobalTheory.CuspRep.IsStable W → (↑S : Set (Sm E N)) ⊆ W → U ≤ W

def SplitInv {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (U : Submodule ℂ (Sm E N)) : Prop :=
  ∀ φ ∈ U, ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g

def RegAll {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (U : Submodule ℂ (Sm E N)) : Prop :=
  ∀ τ : E →+* ℂ, ∃ m, HasInfCharGL U τ m ∧ m.Nodup

def Hyp {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (τ : E →+* ℂ) (U : Submodule ℂ (Sm E N)) : Prop :=
  IsAutSt U ∧ FinGen U ∧ NonPos U ∧ CentIm U ∧ (∃ m, HasInfCharGL U τ m ∧ m.Nodup) ∧ RegAll U

def Conc {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (U : Submodule ℂ (Sm E N)) (φ : Sm E N) : Prop :=
  ∃ (t : Tr E N) (T : Sm E N →ₗ[ℂ] Sm E N), t.Good ∧ t.AllLeaves (fun M _ => 0 < M) ∧
    (∀ o, ∀ ψ ∈ U, T (act o ψ) = act o (T ψ)) ∧ (∀ ψ ∈ U, T ψ ∈ t.space) ∧ T φ ≠ 0

def SliceU : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ), 0 < r → 0 < s → ∀ U : Submodule ℂ (Sm E (r + s)), IsAutSt U →
  FinGen U → SplitInv U → RegAll U → ∀ φ ∈ U, ∀ c ∈ Exp r φ.1, ∃ T, IsSliceMap U c T ∧ T φ ≠ 0

def Blocks : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ) (τ : E →+* ℂ), 0 < r → 0 < s → ∀ U : Submodule ℂ (Sm E (r + s)), Hyp τ U →
  SplitInv U → ∀ (c : ℂ) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)), IsSliceMap U c T → pE E (r + s) r c = 0 →
  ∃ (J : Finset ℕ) (P : ℕ → Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) (W₁ : ℕ → Submodule ℂ (Sm E r))
    (W₂ : ℕ → Submodule ℂ (Sm E s)), (∀ j ∈ J, Hyp τ (W₁ j) ∧ Hyp τ (W₂ j)) ∧
    (∀ j ∈ J, ∀ o, ∀ ψ ∈ U, P j (act o (T ψ)) = act o (P j (T ψ))) ∧ (∀ ψ ∈ U, ∑ j ∈ J, P j (T ψ) = T ψ) ∧
    ∀ j ∈ J, ∀ ψ ∈ U, MemInd2 (tw (W₁ j) ((s : ℂ) / 2)) (tw (W₂ j) (-(r : ℂ) / 2)) (P j (T ψ))

def Leaf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (τ : E →+* ℂ), 0 < N →
  ∀ U : Submodule ℂ (Sm E N), Hyp τ U → ∀ φ ∈ U, (∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, pE E N r c < 0) → φ ≠ 0 →
    Conc U φ

def Node : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ), 0 < r → 0 < s → ∀ (U : Submodule ℂ (Sm E (r + s))) (W₁ : Submodule ℂ (Sm E r))
  (W₂ : Submodule ℂ (Sm E s)) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)), IsAutSt U → IsAutSt W₁ → IsAutSt W₂ →
  (∀ o, ∀ ψ ∈ U, T (act o ψ) = act o (T ψ)) →
  (∀ ψ ∈ U, MemInd2 (tw W₁ ((s : ℂ) / 2)) (tw W₂ (-(r : ℂ) / 2)) (T ψ)) →
  (∀ ψ ∈ W₁, ψ ≠ 0 → Conc W₁ ψ) → (∀ ψ ∈ W₂, ψ ≠ 0 → Conc W₂ ψ) → ∀ φ ∈ U, T φ ≠ 0 → Conc U φ

def Types : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
  (W : Submodule ℂ (Kinf E N → ℂ)), FiniteDimensional ℂ W →
  ∃ Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)), (∀ M, (Ω M).Finite ∧ ∀ W' ∈ Ω M, FiniteDimensional ℂ W') ∧
  ∀ K : Subgroup (GL (Fin N) (Af E)), IsOpen (K : Set (GL (Fin N) (Af E))) →
  ∃ Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))),
    (∀ M, (Θ M).Finite ∧ ∀ K' ∈ Θ M, IsOpen (K' : Set (GL (Fin M) (Af E)))) ∧
    ∀ (t : Tr E N) (f : Sm E N), t.Good → f ∈ t.space → f ≠ 0 → TypeB K W f →
      t.AllLeaves (fun M V => ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V)

def TwConc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (U : Submodule ℂ (Sm E N)) (z : ℂ), z.re = 0 →
  IsAutSt U → ∀ φ ∈ U, Conc U φ → Conc (tw U z) (mulChi N (GlobalTheory.CuspRep.Model.absC E z) φ)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem central_mulChi {a : ℕ} (e w : ℂ) (ψ : Sm E a)
    (hψ : ∀ (t : ℝ) m, ψ.1 (splitCentre E a t * m) = Complex.exp (e * t) * ψ.1 m) (t : ℝ) (m : GA E a) :
    (mulChi a (Model.absC E w) ψ).1 (splitCentre E a t * m) =
      Complex.exp ((e + w * a * (Module.finrank ℚ E : ℂ)) * t) * (mulChi a (Model.absC E w) ψ).1 m := by
  rw [mulChi_apply, mulChi_apply, map_mul, Units.val_mul, hψ, ExponentTwist.splitCentre_eq, ExponentTwist.chiDet_aT le_rfl,
    add_mul, Complex.exp_add]
  ring

theorem centIm_tw {a : ℕ} (V : Submodule ℂ (Sm E a)) (e w : ℂ) (he : (e + w * a * (Module.finrank ℚ E : ℂ)).re = 0)
    (hV : ∀ φ ∈ V, ∀ (t : ℝ) m, φ.1 (splitCentre E a t * m) = Complex.exp (e * t) * φ.1 m) :
    SpectralAccumulation.CentIm (tw V w) := by
  refine ⟨_, he, fun φ hφ t g => ?_⟩
  obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hφ
  exact central_mulChi e w ψ (hV ψ hψ) t g

omit [IsCMField E] in
theorem finrank_ne_zero' : (Module.finrank ℚ E : ℝ) ≠ 0 := by
  have : 0 < Module.finrank ℚ E := Module.finrank_pos
  exact_mod_cast this.ne'

theorem re_of_pE {r s : ℕ} {c : ℂ} (hc : pE E (r + s) r c = 0) :
    c.re = (r : ℝ) * s * (Module.finrank ℚ E : ℝ) / 2 := by
  have hd := finrank_ne_zero' (E := E)
  unfold pE at hc
  push_cast at hc
  field_simp at hc
  linarith

theorem centIm_left {r s : ℕ} (V : Submodule ℂ (Sm E r)) {c : ℂ} (hc : pE E (r + s) r c = 0)
    (hV : ∀ φ ∈ V, ∀ (t : ℝ) m, φ.1 (splitCentre E r t * m) = Complex.exp (c * t) * φ.1 m) :
    SpectralAccumulation.CentIm (tw V (-(s : ℂ) / 2)) := by
  refine centIm_tw V c _ ?_ hV
  have h := re_of_pE (E := E) hc
  have e1 : (c + -(s : ℂ) / 2 * r * (Module.finrank ℚ E : ℂ)).re = c.re - (s : ℝ) / 2 * r * (Module.finrank ℚ E : ℝ) := by
    simp [Complex.add_re, Complex.mul_re, Complex.neg_re] <;> ring_nf
  rw [e1, h]; ring

theorem centIm_right {r s : ℕ} (V : Submodule ℂ (Sm E s)) {c : ℂ} (hc : pE E (r + s) r c = 0)
    (hV : ∀ φ ∈ V, ∀ (t : ℝ) m, φ.1 (splitCentre E s t * m) = Complex.exp (-c * t) * φ.1 m) :
    SpectralAccumulation.CentIm (tw V ((r : ℂ) / 2)) := by
  refine centIm_tw V (-c) _ ?_ hV
  have h := re_of_pE (E := E) hc
  have e1 : (-c + (r : ℂ) / 2 * s * (Module.finrank ℚ E : ℂ)).re = -c.re + (r : ℝ) / 2 * s * (Module.finrank ℚ E : ℝ) := by
    simp [Complex.add_re, Complex.mul_re, Complex.neg_re] <;> ring_nf
  rw [e1, h]; ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

end
end

section

noncomputable section

open NumberField MeasureTheory ComplexConjugate
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

section Defs

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

def GrowP (f : GA E N → ℂ) : Prop :=
  Continuous f ∧ (∀ γ ∈ latticeGL E N, ∀ g, f (γ * g) = f g) ∧
    ∀ ε : ℝ, 0 < ε → An.Bnd f fun r => An.rho E N r + ε

def GrowQ (f : GA E N → ℂ) : Prop :=
  Continuous f ∧ (∀ γ ∈ latticeGL E N, ∀ g, f (γ * g) = f g) ∧
    ∃ κ : ℕ → ℝ, (∀ r, 0 < r → r < N → κ r < An.rho E N r) ∧ An.Bnd f κ

def pr (f g : GA E N → ℂ) : ℂ := pet (latticeGL E N) (Measure.haar : Measure (GA E N)) f g

end Defs

def GrowPHolds : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (χ : Sm E N),
  IsAutForm χ → (∀ (t : ℝ) g, χ.1 (splitCentre E N t * g) = χ.1 g) →
  (∀ r, 0 < r → r < N → ∀ c ∈ Exp r χ.1, pE E N r c ≤ 0) → GrowP χ.1

def GrowQHolds : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (u : Sm E N),
  IsAutForm u → IsSqInt u.1 → GrowQ u.1

def IntBnd : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (H : GA E N → ℝ),
  Continuous H → (∀ g, 0 ≤ H g) → (∀ γ ∈ latticeGL E N, ∀ g, H (γ * g) = H g) →
  ∀ m : ℕ → ℝ, (∀ r, 0 < r → r < N → m r < 2 * An.rho E N r) → An.Bnd (fun g => (H g : ℂ)) m →
    ∫⁻ g in stdDom (latticeGL E N), ENNReal.ofReal (H g) ∂(Measure.haar : Measure (GA E N)) < ⊤

def PairLin : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ),
  (∀ (f₁ f₂ g : GA E N → ℂ) (c : ℂ), GrowP f₁ → GrowP f₂ → GrowQ g →
    pr (f₁ + f₂) g = pr f₁ g + pr f₂ g ∧ pr (c • f₁) g = c * pr f₁ g) ∧
  ∀ (f g₁ g₂ : GA E N → ℂ) (c : ℂ), GrowP f → GrowQ g₁ → GrowQ g₂ →
    pr f (g₁ + g₂) = pr f g₁ + pr f g₂ ∧ pr f (c • g₁) = conj c * pr f g₁

def PairRt : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (x : GA E N)
  (f g : GA E N → ℂ), (∀ γ ∈ latticeGL E N, ∀ y, f (γ * y) = f y) → (∀ γ ∈ latticeGL E N, ∀ y, g (γ * y) = g y) →
    pr (fun y => f (y * x)) g = pr f (fun y => g (y * x⁻¹))

def PairLie : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (X : Lie E N)
  (χ u : Sm E N), GrowP χ.1 → GrowP (act (.lie X) χ).1 → GrowQ u.1 → GrowQ (act (.lie X) u).1 →
    pr (act (.lie X) χ).1 u.1 = -pr χ.1 (act (.lie X) u).1

def Core : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (U : Submodule ℂ (Sm E N)),
  _root_.GlobalTheory.CuspRep.IsStable U → (∀ χ ∈ U, IsAutForm χ) → (∀ χ ∈ U, GrowP χ.1) → ∀ φ ∈ U, φ ∈ A2 E N → φ ≠ 0 →
    ∃ (V : Submodule ℂ (Sm E N)) (p : Sm E N →ₗ[ℂ] Sm E N), IsDiscrete V ∧ (∀ χ ∈ U, p χ ∈ V) ∧
      (∀ o, ∀ χ ∈ U, p (act o χ) = act o (p χ)) ∧ p φ ≠ 0

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

end
end

section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin GlobalTheory.BlockCap PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

theorem rel_expand (G : Sm E (r + s)) (hu : ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), G.1 (unip x * g) = G.1 g)
    (τ : E →+* ℂ) (c : ℂ → ℂ) (hcap : ∀ u, cap τ u G = c u • G) {k : ℕ} (b : Fin k → Sm E r) (q : Fin k → Sm E s)
    (hG : ∀ p, G.1 (lev (Ad E) r s p) = ∑ i, (b i).1 p.1 * (q i).1 p.2) (u : ℂ) (p : GA E r × GA E s) :
    ∑ i, (cap τ (u - (s : ℂ) / 2) (b i)).1 p.1 * (cap τ (u + (r : ℂ) / 2) (q i)).1 p.2 =
      c u * ∑ i, (b i).1 p.1 * (q i).1 p.2 := by
  have h1 := CapFactor.cap_levi E r s τ u G hu p
  rw [hcap] at h1
  have hH : ∀ p', (capR r s τ (u - (s : ℂ) / 2) G).1 (lev (Ad E) r s p') =
      ∑ i, (cap τ (u - (s : ℂ) / 2) (b i)).1 p'.1 * (q i).1 p'.2 :=
    fun p' => capR_expand (n := ![r, s]) τ _ G b q hG p'
  have h2 := capS_expand (n := ![r, s]) τ (u + (r : ℂ) / 2) (capR r s τ (u - (s : ℂ) / 2) G)
    (fun i => cap τ (u - (s : ℂ) / 2) (b i)) q hH p
  rw [← hG p]
  change c u * G.1 _ = _ at h1
  rw [h1]
  exact h2.symm

theorem tensL_apply (N : ℕ) (f : ℕ → Module.End ℂ (Sm E r)) (u : ℂ) {k : ℕ} (b : Fin k → Sm E r) (q : Fin k → Sm E s) :
    (∑ j ∈ Finset.range N, u ^ j • tensOp (f j) LinearMap.id) (fun p : GA E r × GA E s => ∑ i, (b i).1 p.1 * (q i).1 p.2) =
      fun p => ∑ i, ((∑ j ∈ Finset.range N, u ^ j • f j) (b i)).1 p.1 * (q i).1 p.2 := by
  funext p
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, tensOp_sum, Pi.smul_apply, smul_eq_mul,
    Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, LinearMap.id_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem tensR_apply (N : ℕ) (f : ℕ → Module.End ℂ (Sm E s)) (u : ℂ) {k : ℕ} (b : Fin k → Sm E r) (q : Fin k → Sm E s) :
    (∑ j ∈ Finset.range N, u ^ j • tensOp LinearMap.id (f j)) (fun p : GA E r × GA E s => ∑ i, (b i).1 p.1 * (q i).1 p.2) =
      fun p => ∑ i, (b i).1 p.1 * ((∑ j ∈ Finset.range N, u ^ j • f j) (q i)).1 p.2 := by
  funext p
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, tensOp_sum, Pi.smul_apply, smul_eq_mul,
    Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, LinearMap.id_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem fd_tens2 (Z₁ : Submodule ℂ (Sm E r)) (Z₂ : Submodule ℂ (Sm E s)) [FiniteDimensional ℂ Z₁]
    [FiniteDimensional ℂ Z₂] : FiniteDimensional ℂ (tens2 Z₁ Z₂) := by
  classical
  let B₁ := Module.finBasis ℂ Z₁
  let B₂ := Module.finBasis ℂ Z₂
  let f : Fin (Module.finrank ℂ Z₁) × Fin (Module.finrank ℂ Z₂) → (GA E r × GA E s → ℂ) :=
    fun ij m => (B₁ ij.1).1.1 m.1 * (B₂ ij.2).1.1 m.2
  have hle : tens2 Z₁ Z₂ ≤ Submodule.span ℂ (Set.range f) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    have e₁ := B₁.sum_repr ⟨φ₁, h₁⟩
    have e₂ := B₂.sum_repr ⟨φ₂, h₂⟩
    have e : (fun m : GA E r × GA E s => φ₁.1 m.1 * φ₂.1 m.2) =
        ∑ ij : Fin (Module.finrank ℂ Z₁) × Fin (Module.finrank ℂ Z₂), (B₁.repr ⟨φ₁, h₁⟩ ij.1 * B₂.repr ⟨φ₂, h₂⟩ ij.2) • f ij := by
      funext m
      have a₁ := congrArg (fun x : Z₁ => x.1.1 m.1) e₁
      have a₂ := congrArg (fun x : Z₂ => x.1.1 m.2) e₂
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at a₁ a₂
      change φ₁.1 m.1 * φ₂.1 m.2 = _
      rw [← a₁, ← a₂, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, f]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact Submodule.sum_mem _ fun ij _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ij, rfl⟩)
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) := FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
  exact Submodule.finiteDimensional_of_le hle

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

end
end
