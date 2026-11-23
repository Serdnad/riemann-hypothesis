module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs.ExponentTwist

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem card_places : ((Module.finrank ℚ E : ℕ) : ℂ) = 2 * (Fintype.card (InfinitePlace E) : ℂ) := by
  rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  push_cast; ring

omit [_root_.NumberField.IsTotallyComplex E] in
theorem chiDet_absC_val (a : ℕ) (s : ℂ) (g : GA E a) :
    ((chiDet a (Model.absC E s) g : ℂˣ) : ℂ) =
      Complex.exp (s * (GlobalTheory.Mem.Chr.CharModel.logNorm E (Matrix.GeneralLinearGroup.det g) : ℂ)) := rfl

theorem sum_ite_lt {N r : ℕ} (h : r ≤ N) (t : ℂ) :
    ∑ i : Fin N, (if (i : ℕ) < r then t else 0) = r * t := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < r then t else 0), Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [show Finset.filter (fun x => x < r) (Finset.range N) = Finset.range r by ext x; simp; omega]
  simp

theorem det_aInf_apply {N r : ℕ} (h : r ≤ N) (t : ℝ) (w : InfinitePlace E) :
    ((Matrix.GeneralLinearGroup.det (aInf E N r t) : (Cinf E)ˣ) : Cinf E) w = Complex.exp ((r * t : ℝ) : ℂ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change (Matrix.diagonal fun (i : Fin N) (_ : InfinitePlace E) => Complex.exp (if (i : ℕ) < r then (t : ℂ) else 0)).det w = _
  rw [Matrix.det_diagonal, Finset.prod_apply, ← Complex.exp_sum, sum_ite_lt h]
  push_cast; rfl

theorem chiDet_aT {N r : ℕ} (h : r ≤ N) (z : ℂ) (t : ℝ) :
    ((chiDet N (Model.absC E z) (aT E N r t) : ℂˣ) : ℂ) = Complex.exp (z * r * (Module.finrank ℚ E : ℂ) * t) := by
  rw [chiDet_absC_val, aT, det_infGL, Model.logNorm_infId]
  simp only [det_aInf_apply h, Complex.norm_exp_ofReal, Real.log_exp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [card_places]
  congr 1
  push_cast; ring

theorem splitCentre_eq (a : ℕ) (t : ℝ) : splitCentre E a t = aT E a a t := by
  refine congrArg (infGL E a) (Units.ext ?_)
  change Matrix.scalar (Fin a) (expU fun _ : InfinitePlace E => (t : ℂ)).val = Matrix.diagonal _
  ext i j
  simp [Matrix.scalar_apply, expU]

end PositivityTheory.Rg.Rs.ExponentTwist
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace PositivityTheory.Rg.Rs.SatakeVectors

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem absNorm_cpow_ne_zero (w : HeightOneSpectrum (𝓞 E)) (s : ℂ) :
    (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ s) ≠ 0 := by
  have h : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (NumberField.HeightOneSpectrum.one_lt_absNorm w).ne_bot
  exact fun e => h ((Complex.cpow_eq_zero_iff _ _).1 e).1

def qU (w : HeightOneSpectrum (𝓞 E)) (s : ℂ) : ℂˣ :=
  Units.mk0 (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ s) (absNorm_cpow_ne_zero w s)

@[simp] theorem qU_val (w : HeightOneSpectrum (𝓞 E)) (s : ℂ) :
    ((qU w s : ℂˣ) : ℂ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ s := rfl

def SatLike {m : ℕ} (U : Submodule ℂ (Sm E m)) (w : HeightOneSpectrum (𝓞 E)) (S : Multiset ℂˣ) : Prop :=
  ∀ ψ ∈ U, (∀ k ∈ GlobalTheory.LFun.KGL w (n := m), finRep E m (locGL E m w k) ψ = ψ) → ψ ≠ 0 →
    GlobalTheory.LFun.IsSatVecGL w ((finRep E m).comp (locGL E m w)) ψ S

theorem satLike_of_satV {m : ℕ} {V : Submodule ℂ (Sm E m)} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    (h : SatV V w B) : SatLike V w B := h.2

theorem satTw_eq (w : HeightOneSpectrum (𝓞 E)) (z : ℂ) (B : Multiset ℂˣ) :
    satTw w z B = (B.map (· * qU w (-z))).map fun b : ℂˣ => (b : ℂ) := by
  simp [satTw, Multiset.map_map, Function.comp_def]

end PositivityTheory.Rg.Rs.SatakeVectors

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

def Dich : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ), 1 ≤ N → ∀ V : Submodule ℂ (Sm E N), IsDiscrete V →
  (∃ π : CuspSub E N, π.IsUnitary ∧ IsNormalised π ∧ ∀ π', π.Iso π' → AscEmb V π' 1) ∨ ∃ r, 0 < r ∧ r < N ∧ (ExpV r V).Nonempty

def ExpFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ r, 0 < r → r < N → (ExpV r V).Finite

def ExpNeg : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (φ : Sm E N), IsAutForm φ → IsSqInt φ.1 →
  ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, pE E N r c < 0

def SqIntCrit : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (φ : Sm E N), IsAutForm φ → (∀ t g, φ.1 (splitCentre E N t * g) = φ.1 g) →
  (∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, pE E N r c < 0) → IsSqInt φ.1

def ExpTw : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (φ : Sm E N) (z : ℂ), IsAutForm φ →
  ∀ r, 0 < r → r < N → ∀ c ∈ Exp r (mulChi N (GlobalTheory.CuspRep.Model.absC E z) φ).1,
    c - z * r * (Module.finrank ℚ E : ℂ) ∈ Exp r φ.1

def Slice : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ), 0 < r → 0 < s → ∀ V : Submodule ℂ (Sm E (r + s)), IsDiscrete V →
  ∀ c ∈ ExpV r V, ∃ T, IsSliceMap V c T

def TwistedSlicesSquareIntegrable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (V : Submodule ℂ (Sm E (r + s)))
    (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) (z₁ z₂ : ℂ) : Prop :=
  ∀ φ ∈ V, ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)),
    (∀ m₂, ∃ ψ : Sm E r, IsAutForm ψ ∧ IsSqInt ψ.1 ∧ ∀ m₁, (mulChi r (GlobalTheory.CuspRep.Model.absC E z₁) ψ).1 m₁ =
      (T φ).1 (lev (Ad E) r s (m₁, m₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) ∧
    ∀ m₁, ∃ ψ : Sm E s, IsAutForm ψ ∧ IsSqInt ψ.1 ∧ ∀ m₂, (mulChi s (GlobalTheory.CuspRep.Model.absC E z₂) ψ).1 m₂ =
      (T φ).1 (lev (Ad E) r s (m₁, m₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))

def Chord : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ), 0 < r → 0 < s → ∀ (V : Submodule ℂ (Sm E (r + s))) (c : ℂ) (T) (lam : ℝ), 0 < lam →
  IsSliceMap V c T → pE E (r + s) r c = -lam * (r * s) →
  (∀ m, 0 < m → m < r + s → ∀ c' ∈ ExpV m V, pE E (r + s) m c' ≤ -lam * (m * ((r + s : ℕ) - m : ℝ))) →
  TwistedSlicesSquareIntegrable V T (c / (r * (Module.finrank ℚ E : ℂ))) (-c / (s * (Module.finrank ℚ E : ℂ)))

def A2 (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) : Submodule ℂ (Sm E N) :=
  Submodule.span ℂ {ψ | IsAutForm ψ ∧ IsSqInt ψ.1}

def Pr : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ), _root_.GlobalTheory.CuspRep.IsStable (A2 E N) ∧ ∀ ψ ∈ A2 E N, ψ ≠ 0 →
  ∃ (V : Submodule ℂ (Sm E N)) (p : Sm E N →ₗ[ℂ] Sm E N), IsDiscrete V ∧ (∀ χ ∈ A2 E N, p χ ∈ V) ∧
    (∀ o, ∀ χ ∈ A2 E N, p (act o χ) = act o (p χ)) ∧ p ψ ≠ 0

def SliceTens : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (V : Submodule ℂ (Sm E (r + s))), IsDiscrete V →
  ∀ (c z₁ z₂ : ℂ) (T), IsSliceMap V c T → TwistedSlicesSquareIntegrable V T z₁ z₂ → ∀ φ ∈ V, MemInd2 (tw (A2 E r) z₁) (tw (A2 E s) z₂) (T φ)

def IndMap : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (V : Submodule ℂ (Sm E (r + s))) (U₁ : Submodule ℂ (Sm E r))
  (U₂ : Submodule ℂ (Sm E s)) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) (f₁ : Sm E r →ₗ[ℂ] Sm E r) (f₂ : Sm E s →ₗ[ℂ] Sm E s),
  _root_.GlobalTheory.CuspRep.IsStable V → (∀ φ ∈ V, IsAutForm φ) → _root_.GlobalTheory.CuspRep.IsStable U₁ → _root_.GlobalTheory.CuspRep.IsStable U₂ → (∀ o, ∀ φ ∈ V, T (act o φ) = act o (T φ)) →
  (∀ φ ∈ V, MemInd2 U₁ U₂ (T φ)) → (∀ o, ∀ ψ ∈ U₁, f₁ (act o ψ) = act o (f₁ ψ)) →
  (∀ o, ∀ ψ ∈ U₂, f₂ (act o ψ) = act o (f₂ ψ)) →
  ∃ T' : Sm E (r + s) →ₗ[ℂ] Sm E (r + s), (∀ o, ∀ φ ∈ V, T' (act o φ) = act o (T' φ)) ∧
    (∀ φ ∈ V, ∀ (x : BlockIx (r + s) r → Ad E) g, (T' φ).1 (unip x * g) = (T' φ).1 g) ∧
    ∀ φ ∈ V, ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (n : ℕ) (ψ₁ : Fin n → Sm E r) (ψ₂ : Fin n → Sm E s),
      (∀ i, ψ₁ i ∈ U₁) → (∀ i, ψ₂ i ∈ U₂) →
      (∀ m : GA E r × GA E s, (T φ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
        ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) →
      ∀ m : GA E r × GA E s, (T' φ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
        ∑ i, (f₁ (ψ₁ i)).1 m.1 * (f₂ (ψ₂ i)).1 m.2

def Proj : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ), 0 < r → 0 < s → ∀ V : Submodule ℂ (Sm E (r + s)), IsDiscrete V →
  ∀ (c z₁ z₂ : ℂ) (T), IsSliceMap V c T → TwistedSlicesSquareIntegrable V T z₁ z₂ →
  ∃ (V₁ : Submodule ℂ (Sm E r)) (V₂ : Submodule ℂ (Sm E s)), IsDiscrete V₁ ∧ IsDiscrete V₂ ∧
    Emb V (MemInd2 (tw V₁ z₁) (tw V₂ z₂))

def InfInd2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (V : Submodule ℂ (Sm E (r + s))) (V₁ : Submodule ℂ (Sm E r))
  (V₂ : Submodule ℂ (Sm E s)) (z₁ z₂ : ℂ), IsDiscrete V → IsDiscrete V₁ → IsDiscrete V₂ →
  Emb V (MemInd2 (tw V₁ z₁) (tw V₂ z₂)) → ∀ τ m, HasInfCharGL V τ m → ∃ m₁ m₂, HasInfCharGL V₁ τ m₁ ∧
    HasInfCharGL V₂ τ m₂ ∧ m = m₁.map (· + (z₁ - (s : ℂ) / 2)) + m₂.map (· + (z₂ + (r : ℂ) / 2))

def InfAsc : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N a d : ℕ) (V : Submodule ℂ (Sm E N)) (π : CuspSub E a), IsDiscrete V → AscEmb V π d →
  ∀ τ m, HasInfCharGL V τ m → ∃ m₀, π.HasInfChar τ m₀ ∧ m = ∑ i : Fin d, m₀.map (· + (spehExp d i : ℂ))

def SatInd2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (V : Submodule ℂ (Sm E (r + s))) (V₁ : Submodule ℂ (Sm E r))
  (V₂ : Submodule ℂ (Sm E s)) (z₁ z₂ : ℂ), IsDiscrete V → IsDiscrete V₁ → IsDiscrete V₂ →
  Emb V (MemInd2 (tw V₁ z₁) (tw V₂ z₂)) → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
    ∃ B B₁ B₂, SatV V w B ∧ SatV V₁ w B₁ ∧ SatV V₂ w B₂ ∧
      B.map (fun b : ℂˣ => (b : ℂ)) = satTw w (z₁ - (s : ℂ) / 2) B₁ + satTw w (z₂ + (r : ℂ) / 2) B₂

def SatAsc : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N a d : ℕ) (V : Submodule ℂ (Sm E N)) (π : CuspSub E a), IsDiscrete V → AscEmb V π d →
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B₀, (CG.mk π).HasSat w B₀ ∧
    ∀ B, SatV V w B → B.map (fun b : ℂˣ => (b : ℂ)) = ∑ i : Fin d, satTw w (spehExp d i : ℂ) B₀

def SatHerm : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ),
  (∀ V : Submodule ℂ (Sm E N), IsDiscrete V → SatV V w B → B.map (fun b => (star b)⁻¹) = B) ∧
    ∀ π : CuspSub E N, 1 ≤ N → π.IsUnitary → IsNormalised π → (CG.mk π).HasSat w B → B.map (fun b => (star b)⁻¹) = B

def Gap : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ (w : HeightOneSpectrum (𝓞 E))
  (B : Multiset ℂˣ), SatV V w B → ∀ z : ℂ, ‖z‖ < (Ideal.absNorm w.asIdeal : ℝ) ^ (-(1 / 2) : ℝ) →
    (B.map fun b : ℂˣ => (b : ℂ)).count z ≤ (B.map fun b : ℂˣ => (b : ℂ)).count ((Ideal.absNorm w.asIdeal : ℂ) * z)

def StringStep : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ), 0 < r → 0 < s → ∀ (V : Submodule ℂ (Sm E (r + s)))
  (V₁ : Submodule ℂ (Sm E r)) (V₂ : Submodule ℂ (Sm E s)) (z₁ z₂ : ℂ), IsDiscrete V → IsDiscrete V₁ → IsDiscrete V₂ →
  Emb V (MemInd2 (tw V₁ z₁) (tw V₂ z₂)) → ∀ τ, RegInt V τ → (r : ℂ) * z₁ + s * z₂ = 0 → z₁.re < (s : ℝ) / 2 →
  ∀ (a₁ d₁ a₂ d₂ : ℕ) (π₁ : CuspSub E a₁) (π₂ : CuspSub E a₂), π₁.IsUnitary → IsNormalised π₁ → AscEmb V₁ π₁ d₁ →
    π₂.IsUnitary → IsNormalised π₂ → AscEmb V₂ π₂ d₂ →
    (⟨a₁, CG.mk π₁⟩ : Σ b, CG E b) = ⟨a₂, CG.mk π₂⟩ ∧ z₁ = ((s : ℂ) - d₂) / 2 ∧ z₂ = ((d₁ : ℂ) - r) / 2

def Stages : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s a d₁ d₂ : ℕ) (V : Submodule ℂ (Sm E (r + s))) (V₁ : Submodule ℂ (Sm E r))
  (V₂ : Submodule ℂ (Sm E s)) (π : CuspSub E a), IsDiscrete V → IsDiscrete V₁ → IsDiscrete V₂ →
  Emb V (MemInd2 (tw V₁ (((s : ℂ) - d₂) / 2)) (tw V₂ (((d₁ : ℂ) - r) / 2))) → AscEmb V₁ π d₁ → AscEmb V₂ π d₂ →
  AscEmb V π (d₁ + d₂)

def AscAll : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ), 1 ≤ N → ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ τ, RegInt V τ →
  ∃ (a d : ℕ) (π : CuspSub E a), π.IsUnitary ∧ IsNormalised π ∧ ∀ π', π.Iso π' → AscEmb V π' d

end PositivityTheory.Rg.Rs

end
end
